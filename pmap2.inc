type

  twarptype = (w_out, w_both, w_in);
  tproducts = (ore, org, equ);

  tport = record
    v        : boolean;                 // port visible?
    ptype    : byte;                    // port type
    percent  : array[ore..equ] of byte; // port percentages
    quantity : array[ore..equ] of word; // port quantities
  end;

  twarps = record
    warps    : ^word;      // warp array
    warptype : ^twarptype; // warp type for each warp in w
    nw,                    // number of warps
    nwi      : byte;       // number of oneway warps in
  end;

  tbubble = record
    depth    : byte;    // bubble depth
    comp,               // bubble compromised?
    expl     : boolean; // bubble explored?
    bid      : word;    // bubble id
  end;

  tsector = record
    v        : boolean;  // visited?
    figs     : boolean;  // figs?
    wp       : ^twarps;  // warp record
    pt       : ^tport;   // port record
    bu       : ^tbubble; // bubble record
    sid      : ^word;    // secluded id
    ds_to,
    ds_from  : ^byte;    // distances from requested sectors
    notes,
    log : ansistring;
  end;

{
function sortnums(s: ansistring; d: char): ansistring;
function translate(s, tfr, tto: ansistring): ansistring;
function ptypetostr(pt : byte) : ansistring;
function portstr(i, min: word; ps: pointer) : ansistring;
function ptypetoclass(pt : byte) : byte;
procedure showmem;
function spinner(count, width: word): word;
function posc(c:char; s:ansistring): integer;
function validfolder(path:ansistring): boolean;
function paramcheck(p : string) : integer;
function wordloc(s: ansistring; start, num: word; d: char): word;
function wordcount(s: ansistring; d: char): word;
function wordget(s: ansistring; num: word; d: char): ansistring;
procedure readportcim(ps: pointer; ns: word; fname:ansistring; overwrite: byte; fv: boolean; plhandle: pointer);
procedure readztm(ps: pointer; ns: word; fname:ansistring; overwrite: byte; fv: boolean; plhandle: pointer);
procedure readsectorcim(ps: pointer; ns: word; fname:ansistring; overwrite: byte; fv: boolean; plhandle: pointer);
procedure reconcile(ps: pointer; ns: word; pmw, plhandle: pointer);
procedure writesectorcim(ps: pointer; ns: word; fname:ansistring; plhandle: pointer);
procedure writeportcim(ps: pointer; ns: word; fname: ansistring; plhandle: pointer);
function portpairprofitability(ps: pointer; i, j, p: word) : word;
function portpairstr(ps: pointer; i, j : word) : ansistring;
procedure portpairreport(ps: pointer; ns: word; fname: ansistring);
function s_sum(i: word; ps: pointer; mw: word; l, format: byte): ansistring;
procedure bubbleanalysis(ps: pointer; ns, mw: word; fname: ansistring);
procedure blockedports(ps: pointer; ns: word; fname: ansistring);
procedure oneways(ps: pointer; ns: word; fname: ansistring);
procedure secfind(b, i: word; ps, pf: pointer);
procedure secludedanalysis(ps: pointer; ns, mw: word; fname: ansistring);
procedure distcalc(ps: pointer; ns: word; pdlist: pointer; dcount: word);
procedure distancereport(ps: pointer; ns: word; pdlist: pointer; dcount: word; fname: ansistring);
procedure mslcalc(ps: pointer; ns: word; pdlist: pointer; dcount: word; fname: ansistring);
procedure specialportreport(ps: pointer; ns, mw: word; fname: ansistring);
procedure deadends(ps: pointer; ns, mw: word; fname: ansistring);
procedure dumpreport(ps:pointer; ns, mw: word; fname:ansistring);
procedure readfigs(ps: pointer; ns: word; fname: ansistring; plhandle: pointer);
procedure onewaytunnels(ps: pointer; ns: word; fname: ansistring);
procedure writemap(ps: pointer; ns: word; fname: ansistring);
procedure readlog(ps: pointer; ns: word; fname: ansistring; pdlist: pointer; dcount: word);
procedure readnotes(ps: pointer; ns: word; fname: ansistring; pdlist: pointer; dcount: word);
procedure notesreport(ps:pointer; ns, mw: word; fname:ansistring; stype:byte);
function portq(i: word; k: tproducts; ps: pointer; min,max: word) : boolean;
procedure bigportsreport(ps:pointer; ns, mw: word; fname:ansistring);
procedure bubblehunt(ps: pointer; ns, mw: word; fname: ansistring);
}

function translate(s, tfr, tto: ansistring): ansistring;
var
  s2: ansistring;
  i, j, k: longint;
  f: boolean;
begin
  k:=min(length(tfr),length(tto));
  for i:=1 to length(s) do
  begin
    f:=false;
    for j:=1 to k do
      if s[i]=tfr[j] then
      begin
        f:=true;
        break;
      end;
    if f then s2:=s2+tto[j]
    else s2:=s2+s[i];
  end;
  translate:=s2;
end;

function ptypetostr(pt : byte) : ansistring;
var str : ansistring;
begin
  str:='';
  case pt of
    0 : str:='SSS';
    1 : str:='BSS';
    2 : str:='SBS';
    3 : str:='BBS';
    4 : str:='SSB';
    5 : str:='BSB';
    6 : str:='SBB';
    7 : str:='BBB';
  end;
  ptypetostr:=str;
end;

function portstr(i, min: word; ps: pointer) : ansistring;
var
  s: ^tsector;
  str: ansistring;
  quan: word;
  k: tproducts;
begin
  s:=ps;
  if s[i-1].pt=nil then str:=''
  else
    with s[i-1].pt^ do
    begin
      str:=ptypetostr(ptype);
      for k:=ore to equ do
      begin
        if percent[k]=100 then quan:=quantity[k]
        else quan:=(100*quantity[k]) div (percent[k]+1);
        case k of
          ore: if quan<min then str:=lowercase(leftstr(str,1))+rightstr(str,2);
          org: if quan<min then str:=leftstr(str,1)+lowercase(leftstr(rightstr(str,2),1))+rightstr(str,1);
          equ: if quan<min then str:=leftstr(str,2)+lowercase(rightstr(str,1));
        end;
      end;
    end;
  portstr:=str;
end;

function ptypetoclass(pt : byte) : byte;
var pc: byte;
begin
  pc:=0;
  case pt of
    0 : pc:=7;
    1 : pc:=6;
    2 : pc:=5;
    3 : pc:=1;
    4 : pc:=4;
    5 : pc:=2;
    6 : pc:=3;
    7 : pc:=8;
  end;
  ptypetoclass:=pc;
end;

function spinner(count, width: word): word;
var
  x, y: byte;
  ch: char;
begin
  ch:=' ';
  if count=0 then ch:='-';
  if count=width then ch:='\';
  if count=width*2 then ch:='|';
  if count=width*3 then ch:='/';
  if count>=width*4 then
  begin
    ch:='-';
    count:=0;
  end;
  if not(ch=' ') then
  begin
    x:=wherex;
    y:=wherey;
    write(ch);
    gotoxy(x,y);
  end;
  spinner:=count+1;
end;

function posc(c:char; s:ansistring): integer;
var
  p: pchar;
begin
  p:=strscan(pchar(s),c);
  if p=nil then posc:=0
  else posc:=length(s)-strlen(p)+1;
end;

function validfolder(path:ansistring): boolean;
var
  f: text;
  fname: ansistring;
begin
 fname:=path+'pmap.$$$';
 {$i-}
 assign(f, fname);
 rewrite(f);
 {$i+}
 case ioresult of
   0: begin
        write(f,'this file can be deleted.');
        close(f);
        deletefile(fname);
        validfolder:=(extractfilename(fname)='pmap.$$$');
      end;
   otherwise validfolder:=false;
 end;
end;

//function fileexists(fname: string) : boolean;
//var f: file;
//begin
// {$i-}
// assign(f, fname);
// reset(f);
// {$i+}
// fileexists:=(ioresult=0) and (fname<>'');
// close(f);
//end;

function paramcheck(p : string) : integer;
var j, k1, k2, k3, l: integer;
begin
  if posc('/',p)=0 then paramcheck:=0
  else
  begin
    k1:=posc('+',p);
    k2:=posc('-',p);
    k3:=posc(':',p);
    if min(min(k1,k2),k3)=0 then
    begin
      j:=max(max(k1,k2),k3);
      l:=length(p);
      if (j<2) then
      begin
        if (l>1) then paramcheck:=l+1
        else paramcheck:=0;
      end
      else
      begin
        if l>1 then paramcheck:=j
        else paramcheck:=0;
      end;
    end
    else paramcheck:=min(min(k1,k2),k3);
  end;
end;

function wordloc(s: ansistring; start, num: word; d: char): word;
var
  w, l: integer;
  db: boolean;
begin
  l:=length(s);
  if (s='') or (num<1) or (start>l) then
  begin
    wordloc:=0;
    exit;
  end;
  db:=true;
  w:=0;
  start:=pred(start);
  while (w<num) and (start<l) do
  begin
    start:=succ(start);
    if db and not(s[start]=d) then
    begin
      w:=succ(w);
      db:=false;
    end
    else
      if not(db) and (s[start]=d) then db:=true;
  end;
  if w=num then wordloc:=start
  else wordloc:=0;
end;

function wordcount(s: ansistring; d: char): word;
var
  w, i: integer;
  db: boolean;
begin
  if s='' then
  begin
    wordcount:=0;
    exit;
  end;
  db:=true;
  w:=0;
  For  i:=1 to length(s) do
  begin
    if db and not(s[i]=d) then
    begin
      w:=succ(w);
      db:=false;
    end
    else
      if not(db) and (s[i]=d) then db:=true;
  end;
  wordcount:=w;
end;

function wordget(s: ansistring; num: word; d: char): ansistring;
var start, finish : integer;
begin
  if s='' then
  begin
    wordget:='';
    exit;
  end;
  start:=wordloc(s,1,num,d);
  if start=0 then
  begin
    wordget:='';
    exit;
  end
  else finish:=wordloc(s,start,2,d);
  if finish=0 then finish:=succ(length(s));
  repeat
    finish:=pred(finish);
  until s[finish]<>d;
  wordget:=copy(s,start,succ(finish-start));
end;

function sortnums(s: ansistring; d: char): ansistring;
var
  i, j, k, m: word;
  s2: ansistring;
begin
  s2:='';
  for i:=1 to wordcount(s,d) do
  begin
    m:=0;
    for j:=1 to wordcount(s,d) do
    begin
      try
        k:=strtoint(wordget(s,j,d));
      except
        on E : EConvertError do break;
      end;
      m:=max(m,k)
    end;
  end;
  sortnums:=s2;
end;

procedure readportcim(ps: pointer; ns: word; fname:ansistring; overwrite: byte; fv: boolean; plhandle: pointer);
var
  fhandle: text;
  lhandle: ^text;
  line: ansistring;
  sect, j, wc: word;
  k: tproducts;
  port_temp: ^tport;
  s: ^tsector;
  c, mon: word;
  tempstr: ansistring;
  tempint: integer;
begin
  s:=ps;
  lhandle:=plhandle;
  port_temp:=nil;

  if fileexists(fname) then
  begin
    write(lhandle^,' ',fname,': ');
    if length(fname)>33 then write('reading port cim file: ...',rightstr(fname,30),' ')
    else write('reading port cim file: ',fname,' ');
    mon:=spinner(0,500);
    assign(fhandle,fname);
    reset(fhandle);
    c:=0;
    while not(eof(fhandle)) do
    begin
      readln(fhandle,line);
      line:=trim(line);
      wc:=wordcount(line,' ');
      if wc>1 then
      begin
        c+=1;
        mon:=spinner(mon,500);
        try
          sect:=strtoint(wordget(line,1,' '));
        except
          on E : EConvertError do sect:=0;
        end;
        if (sect<=ns) and (sect>0) then
          with s[sect-1] do
          begin
            getmem(port_temp,sizeof(tport));
            port_temp^.v:=fv;
            port_temp^.ptype:=0;
            j:=2;
            for k:=ore to equ do
            begin
              try
                tempstr:=wordget(line,j,' ');
                j+=1;
                if tempstr='-' then // BUY PRODUCT
                begin
                  port_temp^.ptype+=1 shl byte(k);
                  port_temp^.quantity[k]:=strtoint(wordget(line,j,' '));
                  j+=1;
                  tempstr:=(wordget(line,j,' '));
                  j+=1;
                  port_temp^.percent[k]:=strtoint(leftstr(tempstr,length(tempstr)-1));
                end
                else                // SELL PRODUCT
                begin
                  tempint:=strtoint(tempstr);
                  if tempint<0 then
                  begin
                    port_temp^.ptype+=1 shl byte(k);
                    port_temp^.quantity[k]:=word(abs(tempint))
                  end
                  else port_temp^.quantity[k]:=word(tempint);
                  tempstr:=(wordget(line,j,' '));
                  j+=1;
                  port_temp^.percent[k]:=strtoint(leftstr(tempstr,length(tempstr)-1));
                end;
              except
                on E : EConvertError do
                begin
                  if not(port_temp=nil) then begin freemem(port_temp); port_temp:=nil; end;
                  break;
                end;
              end;
            end;
            if not(port_temp^.v) then
              for k:=ore to equ do
                if port_temp^.percent[k]<100 then
                begin
                  if port_temp^.quantity[k]>0 then
                  begin
                    port_temp^.quantity[k]:=(100*port_temp^.quantity[k]) div (port_temp^.percent[k]+1);
                    port_temp^.percent[k]:=100;
                  end
                  else
                  begin
                    port_temp^.quantity[k]:=0;
                    port_temp^.percent[k]:=0;
                  end;
                end;
            case overwrite of
              0: begin // overwrite
                   if not(pt=nil) then
                   begin
                     freemem(pt);
                     pt:=nil;
                   end;
                   pt:=port_temp;
                   port_temp:=nil;
                 end;
              1: begin // do not overwrite, if nil, then write, else just free the memory
                   if pt=nil then
                   begin
                     pt:=port_temp;
                     port_temp:=nil;
                   end;
                 end;
              2: begin // merge
                   if pt=nil then
                   begin
                     pt:=port_temp;
                     port_temp:=nil;
                   end
                   else
                     for k:=ore to equ do
                       if port_temp^.quantity[k]>pt^.quantity[k] then
                       begin
                         pt^.quantity[k]:=port_temp^.quantity[k];
                         pt^.percent[k]:=port_temp^.percent[k];
                       end;
                 end;
            end;
            if not(port_temp=nil) then // free port_temp
            begin
              freemem(port_temp);
              port_temp:=nil;
            end;
          end;
      end;
    end;
    close(fhandle);
    writeln('.');
    writeln(lhandle^,c,' ports read.');
  end;
end;

procedure readztm(ps: pointer; ns: word; fname:ansistring; plhandle: pointer);
var
  fhandle: text;
  lhandle: ^text;
  line, str1: ansistring;
  sec1, sec2, i, j, m, n, mon: word;
  c: longint;
  warp_temp: ^twarps;
  s: ^tsector;
  flag, flag2: boolean;
  path: ansistring;
begin
  s:=ps;
  lhandle:=plhandle;
  warp_temp:=nil;

  if fileexists(fname) then
  begin
    write(lhandle^,' ',fname,': ');
    if length(fname)>33 then write('reading ztm file: ...',rightstr(fname,30),' ')
    else write('reading ztm file: ',fname,' ');
    mon:=spinner(0,500);
    assign(fhandle,fname);
    reset(fhandle);
    c:=0;
    path:='';
    flag:=false;
    while not(eof(fhandle)) do
    begin
      readln(fhandle,line);
      line:=trim(line);
      if line='' then
      begin
        if flag and not(path='') then
        begin
          try
            sec1:=strtoint(wordget(path,1,' '));
            for i:=2 to wordcount(path,' ') do
              with s[sec1-1] do
              begin
                sec2:=strtoint(wordget(path,i,' '));
                flag2:=false;
                mon:=spinner(mon,500);
                if (sec1<=ns) and (sec1>0) and (sec2<=ns) and (sec2>0) then 
                begin
                  if wp=nil then flag2:=false
                  else
                    for j:=1 to wp^.nw do
                      if (wp^.warps[j-1]=sec2) then begin flag2:=true; break; end;
                  if not(flag2) then
                  begin
                    // warp_temp is one warp only.
                    getmem(warp_temp,sizeof(twarps));
                    getmem(warp_temp^.warps,sizeof(word));
                    getmem(warp_temp^.warptype,sizeof(twarptype));
                    warp_temp^.nw:=1;
                    warp_temp^.nwi:=0;
                    warp_temp^.warps[0]:=sec2;
                    warp_temp^.warptype[0]:=w_out;

                    // following code is same as 'merge' case from readsectorcim below
                    if wp=nil then
                    begin
                      wp:=warp_temp;
                      warp_temp:=nil;
                    end
                    else
                    begin
                      flag:=(warp_temp^.nw=wp^.nw) and not(v);  // if visited, then don't merge warps
                      if flag then
                        for j:=1 to wp^.nw do
                          if not(warp_temp^.warps[j-1]=wp^.warps[j-1]) then flag:=false;
                      if not(flag) then
                      begin
                        // merge data here
                        str1:='';
                        m:=1; n:=1;
                        while (m<=warp_temp^.nw) and (n<=wp^.nw) do
                        begin
                          if warp_temp^.warps[m-1]=wp^.warps[n-1] then
                          begin
                            str1+=inttostr(warp_temp^.warps[m-1])+' ';
                            m+=1;
                            n+=1;
                          end
                          else
                          begin
                            if warp_temp^.warps[m-1]<wp^.warps[n-1] then
                            begin
                              str1+=inttostr(warp_temp^.warps[m-1])+' ';
                              m+=1;
                            end
                            else
                            begin
                              str1+=inttostr(wp^.warps[n-1])+' ';
                              n+=1;
                            end;
                          end;
                        end;
                        if m<=warp_temp^.nw then
                          for j:=m to warp_temp^.nw do
                            str1+=inttostr(warp_temp^.warps[j-1])+' ';
                        if n<=wp^.nw then
                          for j:=n to wp^.nw do
                            str1+=inttostr(wp^.warps[j-1])+' ';
                        if not(wp=nil) then
                        begin
                          if not(wp^.warps=nil) then freemem(wp^.warps);
                          if not(wp^.warptype=nil) then freemem(wp^.warptype);
                          freemem(wp);
                          wp:=nil;
                        end;
                        str1:=trim(str1);
                        getmem(wp,sizeof(twarps));
                        wp^.nw:=wordcount(str1,' ');
                        wp^.nwi:=0;
                        getmem(wp^.warps,(wp^.nw)*sizeof(word));
                        getmem(wp^.warptype,(wp^.nw)*sizeof(twarptype));
                        for j:=1 to wp^.nw do
                        begin
                          wp^.warps[j-1]:=strtoint(wordget(str1,j,' '));
                          wp^.warptype[j-1]:=w_out;
                        end;
                      end;
                    end;
                    if not(warp_temp=nil) then // free warp_temp
                    begin
                      if not(warp_temp^.warps=nil) then freemem(warp_temp^.warps);
                      if not(warp_temp^.warptype=nil) then freemem(warp_temp^.warptype);
                      freemem(warp_temp);
                      warp_temp:=nil;
                    end;
                  end;
                end;
                sec1:=sec2;
              end;
            c+=wordcount(path,' ')-1;
          except
            on E : EConvertError do flag:=false;
          end;
        end;
        path:='';
        flag:=false;
      end;
      if flag then
      begin
        path:=path+' '+translate(line,'()>','   ');
      end;
      if leftstr(line,4)='TO >' then flag:=true;
    end;
    close(fhandle);
    writeln('.');
    writeln(lhandle^,c,' sectors read.');
  end;
end;

procedure readsectorcim(ps: pointer; ns: word; fname:ansistring; overwrite: byte; fv: boolean; plhandle: pointer);
var
  fhandle: text;
  lhandle: ^text;
  line, str1: ansistring;
  sect, i, j, m, n, wc: word;
  warp_temp: ^twarps;
  s: ^tsector;
  c, mon: word;
  flag: boolean;
begin
  s:=ps;
  lhandle:=plhandle;
  warp_temp:=nil;

  if fileexists(fname) then
  begin
    write(lhandle^,' ',fname,': ');
    if length(fname)>33 then write('reading sector cim file: ...',rightstr(fname,30),' ')
    else write('reading sector cim file: ',fname,' ');
    mon:=spinner(0,500);
    assign(fhandle,fname);
    reset(fhandle);
    c:=0;
    while not(eof(fhandle)) do
    begin
      readln(fhandle,line);
      line:=trim(line);
      wc:=wordcount(line,' ');
      if wc>1 then
      begin
        c+=1;
        mon:=spinner(mon,500);
        try
          sect:=strtoint(wordget(line,1,' '));
        except
          on E : EConvertError do sect:=0;
        end;
        if (sect<=ns) and (sect>0) then
          with s[sect-1] do
          begin
            getmem(warp_temp,sizeof(twarps));
            getmem(warp_temp^.warps,(wc-1)*sizeof(word));
            getmem(warp_temp^.warptype,(wc-1)*sizeof(twarptype));
            warp_temp^.nw:=wc-1;
            warp_temp^.nwi:=0;
            for i:=1 to warp_temp^.nw do
            begin
              try
                warp_temp^.warps[i-1]:=strtoint(wordget(line,i+1,' '));
                warp_temp^.warptype[i-1]:=w_out;
              except
                on E : EConvertError do
                begin
                  if not(warp_temp=nil) then
                  begin
                    if not(warp_temp^.warps=nil) then freemem(warp_temp^.warps);
                    if not(warp_temp^.warptype=nil) then freemem(warp_temp^.warptype);
                    freemem(warp_temp);
                    warp_temp:=nil;
                  end;
                  break;
                end;
              end;
            end;
            case overwrite of
              0: begin // overwrite
                   v:=fv;
                   if not(wp=nil) then
                   begin
                     if not(wp^.warps=nil) then freemem(wp^.warps);
                     if not(wp^.warptype=nil) then freemem(wp^.warptype);
                     freemem(wp);
                     wp:=nil;
                   end;
                   wp:=warp_temp;
                   warp_temp:=nil;
                 end;
              1: begin // do not overwrite, if nil, then write, else just free the memory
                   if wp=nil then
                   begin
                     wp:=warp_temp;
                     warp_temp:=nil;
                   end;
                 end;
              2: begin // merge
                   if wp=nil then
                   begin
                     wp:=warp_temp;
                     warp_temp:=nil;
                   end
                   else
                   begin
                     flag:=(warp_temp^.nw=wp^.nw) and not(v);  // if visited, then don't merge warps
                     if flag then
                       for j:=1 to wp^.nw do
                         if not(warp_temp^.warps[j-1]=wp^.warps[j-1]) then flag:=false;
                     if not(flag) then
                     begin
                       // merge data here
                       str1:='';
                       m:=1; n:=1;
                       while (m<=warp_temp^.nw) and (n<=wp^.nw) do
                       begin
                         if warp_temp^.warps[m-1]=wp^.warps[n-1] then
                         begin
                           str1+=inttostr(warp_temp^.warps[m-1])+' ';
                           m+=1;
                           n+=1;
                         end
                         else
                         begin
                           if warp_temp^.warps[m-1]<wp^.warps[n-1] then
                           begin
                             str1+=inttostr(warp_temp^.warps[m-1])+' ';
                             m+=1;
                           end
                           else
                           begin
                             str1+=inttostr(wp^.warps[n-1])+' ';
                             n+=1;
                           end;
                         end;
                       end;
                       if m<=warp_temp^.nw then
                         for j:=m to warp_temp^.nw do
                           str1+=inttostr(warp_temp^.warps[j-1])+' ';
                       if n<=wp^.nw then
                         for j:=n to wp^.nw do
                           str1+=inttostr(wp^.warps[j-1])+' ';
                       if not(wp=nil) then
                       begin
                         if not(wp^.warps=nil) then freemem(wp^.warps);
                         if not(wp^.warptype=nil) then freemem(wp^.warptype);
                         freemem(wp);
                         wp:=nil;
                       end;
                       str1:=trim(str1);
                       getmem(wp,sizeof(twarps));
                       wp^.nw:=wordcount(str1,' ');
                       wp^.nwi:=0;
                       getmem(wp^.warps,(wp^.nw)*sizeof(word));
                       getmem(wp^.warptype,(wp^.nw)*sizeof(twarptype));
                       for j:=1 to wp^.nw do
                       begin
                         wp^.warps[j-1]:=strtoint(wordget(str1,j,' '));
                         wp^.warptype[j-1]:=w_out;
                       end;
                     end;
                   end;
                 end;
            end;
            if not(warp_temp=nil) then // free warp_temp
            begin
              if not(warp_temp^.warps=nil) then freemem(warp_temp^.warps);
              if not(warp_temp^.warptype=nil) then freemem(warp_temp^.warptype);
              freemem(warp_temp);
              warp_temp:=nil;
            end;
          end;
      end;
    end;
    close(fhandle);
    writeln('.');
    writeln(lhandle^,c,' sectors read.');
  end;
end;

procedure reconcile(ps: pointer; ns: word; pmw, plhandle: pointer);
var
  s, ptra, ptrb: ^tsector;
  warp_temp: ^twarps;
  lhandle: ^text;
  mw: ^word;
  i, j, k, m, n, mon, maxwarps: word;
  found, flag: boolean;
begin
  s:=ps; ptra:=nil; ptrb:=nil; warp_temp:=nil; mw:=pmw; lhandle:=plhandle;
  maxwarps:=0;
  mon:=spinner(0,500);
  writeln(lhandle^,' data reconciled.');
  write('reconciling warp data: ');
  for i:=1 to ns do
  begin
    ptra:=@s[i-1];
    if not(ptra^.wp=nil) then
      for j:=1 to ptra^.wp^.nw do
        if ptra^.wp^.warptype[j-1]=w_out then
        begin
          ptrb:=@s[ptra^.wp^.warps[j-1]-1];
          if ptrb^.wp=nil then
          begin
            getmem(warp_temp,sizeof(twarps));
            getmem(warp_temp^.warps,sizeof(word));
            getmem(warp_temp^.warptype,sizeof(twarptype));
            warp_temp^.nw:=1;
            warp_temp^.nwi:=0;
            warp_temp^.warps[0]:=i;
            warp_temp^.warptype[0]:=w_in;
            ptrb^.wp:=warp_temp;
            warp_temp:=nil;
          end
          else
          begin
            found:=false;
            for k:=1 to ptrb^.wp^.nw do
              if i=ptrb^.wp^.warps[k-1] then
              begin
                found:=true;
                ptra^.wp^.warptype[j-1]:=w_both;
                ptrb^.wp^.warptype[k-1]:=w_both;
                break;
              end;
            if not(found) then
            begin
              getmem(warp_temp, sizeof(twarps));
              getmem(warp_temp^.warps,(ptrb^.wp^.nw+1)*sizeof(word));
              getmem(warp_temp^.warptype,(ptrb^.wp^.nw+1)*sizeof(twarptype));
              warp_temp^.nw:=ptrb^.wp^.nw+1;
              maxwarps:=max(maxwarps,warp_temp^.nw);
              warp_temp^.nwi:=ptrb^.wp^.nwi;
              m:=0; n:=0; flag:=true;
              while m<ptrb^.wp^.nw do
              begin
                if (i<ptrb^.wp^.warps[m]) and flag then
                begin
                  warp_temp^.warps[n]:=i;
                  warp_temp^.warptype[n]:=w_in;
                  warp_temp^.nwi+=1;
                  flag:=false;
                  n+=1;
                end;
                warp_temp^.warps[n]:=ptrb^.wp^.warps[m];
                warp_temp^.warptype[n]:=ptrb^.wp^.warptype[m];
                m+=1; n+=1;
              end; // while
              if flag then
              begin
                warp_temp^.warps[warp_temp^.nw-1]:=i;
                warp_temp^.warptype[warp_temp^.nw-1]:=w_in;
                warp_temp^.nwi+=1;
              end;
              if not(ptrb^.wp=nil) then
              begin
                if not(ptrb^.wp^.warps=nil) then freemem(ptrb^.wp^.warps);
                if not(ptrb^.wp^.warptype=nil) then freemem(ptrb^.wp^.warptype);
                freemem(ptrb^.wp);
                ptrb^.wp:=nil;
              end;
              ptrb^.wp:=warp_temp;
              warp_temp:=nil;
            end; // if not found
          end; // else
        end; // if w_out
    ptra:=nil; ptrb:=nil;
    mon:=spinner(mon,500);
  end; // for i
  mw^:=maxwarps;
  writeln('.');
end;

procedure writesectorcim(ps: pointer; ns: word; fname:ansistring; plhandle: pointer);
var
  s: ^tsector;
  fhandle: text;
  lhandle: ^text;
  c, i, j, n, mon: word;
begin
  s:=ps;
  lhandle:=plhandle;
  write(lhandle^,' ',fname,': ');
  if length(fname)>33 then write('writing sector cim file: ...',rightstr(fname,30),' ')
  else write('writing sector cim file: ',fname,' ');
  assign(fhandle, fname);
  rewrite(fhandle);
  mon:=spinner(0,500);
  c:=0;
  for i:=1 to ns do
  begin
    if not(s[i-1].wp=nil) then
    begin
      c+=1;
      if (i<10)    and (ns>9)    then write(fhandle,' ');
      if (i<100)   and (ns>99)   then write(fhandle,' ');
      if (i<1000)  and (ns>999)  then write(fhandle,' ');
      if (i<10000) and (ns>9999) then write(fhandle,' ');
      write(fhandle,i);
      with s[i-1].wp^ do
        for j:=1 to nw do
          if warptype[j-1]<=w_both then
          begin
            n:=warps[j-1];
            if (n<10)    and (ns>9)    then write(fhandle,' ');
            if (n<100)   and (ns>99)   then write(fhandle,' ');
            if (n<1000)  and (ns>999)  then write(fhandle,' ');
            if (n<10000) and (ns>9999) then write(fhandle,' ');
            write(fhandle,' ',n);
          end;
      writeln(fhandle);
      mon:=spinner(mon,500);
    end;
  end;
  close(fhandle);
  writeln('.');
  writeln(lhandle^,c,' sectors written');
end;

procedure writeportcim(ps: pointer; ns: word; fname: ansistring; plhandle: pointer);
var
  s: ^tsector;
  fhandle: text;
  lhandle: ^text;
  c, i, n, mon: word;
  k: tproducts;
begin
  s:=ps;
  lhandle:=plhandle;
  write(lhandle^,' ',fname,': ');
  if length(fname)>33 then write('writing port cim file: ...',rightstr(fname,30),' ')
  else write('writing port cim file: ',fname,' ');
  assign(fhandle, fname);
  rewrite(fhandle);
  mon:=spinner(0,500);
  c:=0;
  for i:=1 to ns do
  begin
    if not(s[i-1].pt=nil) then
    begin
      c+=1;
      if (i<10)    and (ns>9)    then write(fhandle,' ');
      if (i<100)   and (ns>99)   then write(fhandle,' ');
      if (i<1000)  and (ns>999)  then write(fhandle,' ');
      if (i<10000) and (ns>9999) then write(fhandle,' ');
      write(fhandle,i);
      with s[i-1].pt^ do
        for k:=ore to equ do
        begin
          case k of
            ore: n:=1;
            org: n:=2;
            equ: n:=4;
          end;
          if (n and ptype)=n then write(fhandle,' -')
          else write(fhandle,'  ');
          n:=quantity[k];
          if (n<10)    then write(fhandle,' ');
          if (n<100)   then write(fhandle,' ');
          if (n<1000)  then write(fhandle,' ');
          if (n<10000) then write(fhandle,' ');
          write(fhandle,n,' ');
          n:=percent[k];
          if (n<10)  then write(fhandle,' ');
          if (n<100) then write(fhandle,' ');
          write(fhandle,n,'%');
        end;
      writeln(fhandle);
      mon:=spinner(mon,500);
    end;
  end;
  close(fhandle);
  writeln('.');
  writeln(lhandle^,c,' ports written.');
end;

function portpairprofitability(ps: pointer; i, j, p: word) : word;
var
  s: ^tsector;
  c, n1f, n1o, n1e, n2f, n2o, n2e: longint;
begin
  s:=ps;
  c:=0;
  if ((s[i-1].pt^.ptype=3) and (s[j-1].pt^.ptype=4)) then c:=1;
  if ((s[i-1].pt^.ptype=5) and (s[j-1].pt^.ptype=2)) then c:=2;
  if ((s[i-1].pt^.ptype=6) and (s[j-1].pt^.ptype=1)) then c:=3;
  if ((s[i-1].pt^.ptype=0) and (s[j-1].pt^.ptype=7)) then c:=4;
  if ((s[i-1].pt^.ptype=3) and (s[j-1].pt^.ptype=5)) then c:=5;
  if ((s[i-1].pt^.ptype=4) and (s[j-1].pt^.ptype=2)) then c:=6;
  if ((s[i-1].pt^.ptype=3) and (s[j-1].pt^.ptype=6)) then c:=7;
  if ((s[i-1].pt^.ptype=4) and (s[j-1].pt^.ptype=1)) then c:=8;
  if ((s[i-1].pt^.ptype=5) and (s[j-1].pt^.ptype=6)) then c:=9;
  if ((s[i-1].pt^.ptype=2) and (s[j-1].pt^.ptype=1)) then c:=10;
  if (p>=100) then c:=0;

//  writeln('case=',c,' ',i,' ',j);
//  with s[i-1].pt^ do writeln(quantity[ore],' ',quantity[org],' ',quantity[equ]);
//  with s[j-1].pt^ do writeln(quantity[ore],' ',quantity[org],' ',quantity[equ]);

  with s[i-1].pt^ do n1f:=max(quantity[ore]-trunc((quantity[ore]*100/max(percent[ore],1))*p/100),0);
  with s[i-1].pt^ do n1o:=max(quantity[org]-trunc((quantity[org]*100/max(percent[org],1))*p/100),0);
  with s[i-1].pt^ do n1e:=max(quantity[equ]-trunc((quantity[equ]*100/max(percent[equ],1))*p/100),0);
  with s[j-1].pt^ do n2f:=max(quantity[ore]-trunc((quantity[ore]*100/max(percent[ore],1))*p/100),0);
  with s[j-1].pt^ do n2o:=max(quantity[org]-trunc((quantity[org]*100/max(percent[org],1))*p/100),0);
  with s[j-1].pt^ do n2e:=max(quantity[equ]-trunc((quantity[equ]*100/max(percent[equ],1))*p/100),0);
  case c of
    0 : portpairprofitability:=0;
    1 : portpairprofitability:=min(min(n1e,n2e),min(n1o,n2o)); //min(min(n1e,n2e),min(n1f+n1o,n2f+n2o));
    2 : portpairprofitability:=min(min(n1o,n2o),min(n1e,n2e)); //min(min(n1o,n2o),min(n1f+n1e,n2f+n2e));
    3 : portpairprofitability:=min(min(n1f,n2f),min(n1e,n2e)); //min(min(n1f,n2f),min(n1o+n1e,n2o+n2e));
    4 : portpairprofitability:=min(n1f+n1o+n1e,n2f+n2o+n2e) div 2;
    5,6 : portpairprofitability:=min(min(n1o,n1e),min(n2o,n2e));
    7,8 : portpairprofitability:=min(min(n1f,n1e),min(n2f,n2e));
    9,10 : portpairprofitability:=min(min(n1f,n1o),min(n2f,n2o));
    otherwise portpairprofitability:=0;
  end;
end;

function portpairstr(ps: pointer; i, j : word) : ansistring;
var
  s: ^tsector;
  line, str1 : ansistring;
  k: tproducts;
begin
  s:=ps;
  line:='';
  with s[i-1] do
  begin
    str1:=inttostr(i);
    if figs then line:=line+'+'
    else line:=line+' ';
    line:=line+str1+stringofchar(' ',6-length(str1));
    line:=line+portstr(i,3001,s)+' (';
    if not(v) then line:=line+'???'
    else if not(pt^.v) then line:=line+'...'
         else
         begin
           if pt^.percent[ore]=100 then line:=line+'*'
           else line:=line+inttostr(pt^.percent[ore] div 10);
           if pt^.percent[org]=100 then line:=line+'*'
           else line:=line+inttostr(pt^.percent[org] div 10);
           if pt^.percent[equ]=100 then line:=line+'*'
           else line:=line+inttostr(pt^.percent[equ] div 10);
         end;
    line:=line+') - ';
  end;
  with s[j-1] do
  begin
    str1:=inttostr(j);
    if figs then line:=line+'+'
    else line:=line+' ';
    line:=line+str1+stringofchar(' ',6-length(str1));
    line:=line+portstr(j,3001,s)+' (';
    if not(v) then line:=line+'???'
    else if not(pt^.v) then line:=line+'...'
         else
         begin
           if pt^.percent[ore]=100 then line:=line+'*'
           else line:=line+inttostr(pt^.percent[ore] div 10);
           if pt^.percent[org]=100 then line:=line+'*'
           else line:=line+inttostr(pt^.percent[org] div 10);
           if pt^.percent[equ]=100 then line:=line+'*'
           else line:=line+inttostr(pt^.percent[equ] div 10);
         end;
    line:=line+')';
  end;
  if s[i-1].pt^.v and s[j-1].pt^.v then
  begin
    line:=line+' ';
    for k:=ore to equ do
    begin
      if s[i-1].pt^.quantity[k]<10000 then str1:=inttostr(s[i-1].pt^.quantity[k])
      else str1:=inttostr(s[i-1].pt^.quantity[k] div 1000)+'k';
      line:=line+stringofchar(' ',4-length(str1))+str1+'-';
      if s[j-1].pt^.quantity[k]<10000 then str1:=inttostr(s[j-1].pt^.quantity[k])
      else str1:=inttostr(s[j-1].pt^.quantity[k] div 1000)+'k';
      line:=line+str1+stringofchar(' ',4-length(str1));
      if k<equ then line:=line+' / ';
    end;
  end
  else line:=line+'                                  ';
  if ((s[i-1].bu=nil) and (s[j-1].bu=nil)) then str1:='   '
  else str1:=' b ';
  portpairstr:=line+str1+inttostr(portpairprofitability(ps,i,j,50));
end;

procedure portpairreport(ps: pointer; ns: word; fname: ansistring);
var
  s: ^tsector;
  fhandle: text;
  c, i, j, k, mon: word;
const
  p1: array [1..20] of word =(1,2,3,7,1,4,1,4,2,5,2,2,2,2,3,3,3,4,4,8);
  p2: array [1..20] of word =(4,5,6,8,2,5,3,6,3,6,2,3,4,8,3,4,8,4,8,8);
begin
  s:=ps;
  if length(fname)>33 then write('writing port pair report: ...',rightstr(fname,30),' ')
  else write('writing port pair report: ',fname,' ');
  assign(fhandle,fname);
  rewrite(fhandle);
  mon:=spinner(0,500);
  for c:=1 to 20 do
  begin
    case c of
      1 : writeln(fhandle,'triple pairs:');
      5 : writeln(fhandle,'double pairs:  org/equ');
      7 : writeln(fhandle,'double pairs:  ore/equ');
      9 : writeln(fhandle,'double pairs:  ore/org');
      11: writeln(fhandle,'evil pairs:');
    end;
    writeln(fhandle,' specific pairs (',p1[c],':',p2[c],')');
    for i:=1 to ns do
    begin
      mon:=spinner(mon,10000);
      with s[i-1] do
        if not(pt=nil) and not(wp=nil) then
          for j:=1 to wp^.nw do
          begin
            k:=wp^.warps[j-1];
            if not(s[k-1].pt=nil) and not(s[k-1].wp=nil) then
              if not(p1[c]=p2[c]) or ((p1[c]=p2[c]) and (i<k)) then
                if (ptypetoclass(pt^.ptype)=p1[c]) and (ptypetoclass(s[k-1].pt^.ptype)=p2[c]) and (wp^.warptype[j-1]=w_both) then
                  writeln(fhandle,'  ',portpairstr(s,i,k));
          end;
    end;
  end;
  close(fhandle);
  writeln('.');
end;

function s_sum(i: word; ps: pointer; mw: word; l, format: byte): ansistring;
var
  s: ^tsector;
  str1, str2: ansistring;
  sector, port1, port2, port3, msl, sol, gate1, gate2, warps, note1, note2: ansistring;
  j : word;
  flag1, flag2: boolean;
begin
  s:=ps;
  if i=0 then
    case format of
      0: s_sum:=leftstr('sector ',l+3)+' xxx '+'ucd   msl  : warps ^=oneway out, v=oneway in'+stringofchar(' ',(l+5)*mw-30)+'notes';
      1: s_sum:=leftstr('sector ',l+3)+' xxx '+rightstr(' gate',l)+'/ucd   msl  : warps ^=oneway out, v=oneway in'+stringofchar(' ',(l+5)*mw-30)+'notes';
      2: s_sum:=leftstr('sector ',l+3)+' xxx '+rightstr(' gate',l)+'/ucd  : warps ^=oneway out, v=oneway in'+stringofchar(' ',(l+5)*mw-30)+'notes';
      3: s_sum:=leftstr('sector ',l+3)+' xxx (%%%) ore org equ '+rightstr(' gate',l)+'/ucd   msl  : warps ^=oneway out, v=oneway in'+stringofchar(' ',(l+5)*mw-30)+'notes';
      4: s_sum:=leftstr('sector ',l+3)+' xxx '+'ucd   msl   sol  : warps ^=oneway out, v=oneway in'+stringofchar(' ',(l+5)*mw-30)+'notes';
      otherwise s_sum:='';
    end
  else
  begin
    with s[i-1] do
    begin

      // msl string
      if (ds_to[0]=255) or (ds_from[0]=255) then msl:=' n/a '
      else
      begin
        str1:=inttostr(ds_from[0]);
        msl:=stringofchar(' ',2-length(str1))+str1+',';
        str1:=inttostr(ds_to[0]);
        msl:=msl+str1+stringofchar(' ',2-length(str1));
      end;

      // sol string
      if (ds_to[1]=255) or (ds_from[1]=255) then sol:=' n/a '
      else
      begin
        str1:=inttostr(ds_from[1]);
        sol:=stringofchar(' ',2-length(str1))+str1+',';
        str1:=inttostr(ds_to[1]);
        sol:=sol+str1+stringofchar(' ',2-length(str1));
      end;

      // sector string
      sector:=inttostr(i);
      if figs then str2:='+'
      else str2:=' ';
      if v then
      begin
       if pt=nil then sector:=' '+str2+stringofchar(' ',l-length(sector))+sector+' '
       else
       begin
         if not(pt^.v) then sector:='['+str2+stringofchar(' ',l-length(sector))+sector+']'
         else sector:=' '+str2+stringofchar(' ',l-length(sector))+sector+' ';
       end
      end
      else sector:='('+str2+stringofchar(' ',l-length(sector))+sector+')';

      // port strings
      if pt=nil then
      begin
        port1:='---';
        port2:='     ';
        port3:='           ';
      end
      else
      begin
        port1:=portstr(i,3001,s);
        port2:='(';
        if not(pt^.v) then port2:=port2+'.'
        else
          if pt^.percent[ore]=100 then port2:=port2+'*'
          else port2:=port2+inttostr(pt^.percent[ore] div 10);
        if not(pt^.v) then port2:=port2+'.'
        else
          if pt^.percent[org]=100 then port2:=port2+'*'
          else port2:=port2+inttostr(pt^.percent[org] div 10);
        if not(pt^.v) then port2:=port2+'.'
        else
          if pt^.percent[equ]=100 then port2:=port2+'*'
          else port2:=port2+inttostr(pt^.percent[equ] div 10);
        port2:=port2+')';
        if pt^.quantity[ore]>999 then str1:=inttostr(pt^.quantity[ore] div 1000)+'k'
        else str1:=inttostr(pt^.quantity[ore]);
        port3:=stringofchar(' ',3-length(str1))+str1+' ';
        if pt^.quantity[org]>999 then str1:=inttostr(pt^.quantity[org] div 1000)+'k'
        else str1:=inttostr(pt^.quantity[org]);
        port3:=port3+stringofchar(' ',3-length(str1))+str1+' ';
        if pt^.quantity[equ]>999 then str1:=inttostr(pt^.quantity[equ] div 1000)+'k'
        else str1:=inttostr(pt^.quantity[equ]);
        port3:=port3+stringofchar(' ',3-length(str1))+str1;
      end;

      // warp string
      warps:='';
      if not(wp=nil) then
      begin
        for j:=1 to (wp^.nw) do
        begin
          if s[wp^.warps[j-1]-1].figs then str2:='+'
          else str2:=' ';
          str1:=inttostr(wp^.warps[j-1]);
          case wp^.warptype[j-1] of
            w_out:  str1:=str1+'^';
            w_both: str1:=str1+' ';
            w_in:   str1:=str1+'v';
          end;
          if s[wp^.warps[j-1]-1].v then
          begin
            flag1:=not(s[wp^.warps[j-1]-1].pt=nil);
            if flag1 then flag2:=s[wp^.warps[j-1]-1].pt^.v
            else flag2:=true;
            if flag1 and not(flag2) then str1:='['+str2+stringofchar(' ',l-length(str1)+1)+str1+']'
            else str1:=' '+str2+stringofchar(' ',l-length(str1)+1)+str1+' ';
          end
          else str1:='('+str2+stringofchar(' ',l-length(str1)+1)+str1+')';
          warps:=warps+str1;
          if j<wp^.nw then warps:=warps+' ';
        end;
      end;

      // gate strings
      gate1:=stringofchar(' ',l);
      gate2:='    ';
      if not(bu=nil) then
      begin
        if bu^.bid>0 then
        begin
          gate1:=inttostr(bu^.bid);
          gate1:=stringofchar(' ',l-length(gate1))+gate1;

          if bu^.expl then gate2:=' '
          else gate2:='u';
          if bu^.comp then gate2:=gate2+'c'
          else gate2:=gate2+' ';
          str1:=inttostr(bu^.depth);
          gate2:=gate2+str1+stringofchar(' ',2-length(str1));
        end
      end;

      // note string
      if (notes='') and (log='') then
      begin
        note1:='';
        note2:='';
      end
      else
      begin
        if warps='' then note1:=stringofchar(' ',(l+5)*mw)
                    else note1:=stringofchar(' ',(l+5)*(mw-wp^.nw));
        if notes='' then note2:='notes: ('+log+')'
                    else if log='' then note2:='notes: '+notes
                                   else note2:='notes: '+notes+' ('+log+')';
      end;

    end;

    case format of
      0: s_sum:=trimright(sector+' '+port1+' '+gate2+' '+msl+' : '+warps+' '+note1+' '+note2);
      1: s_sum:=trimright(sector+' '+port1+' '+gate1+'/'+gate2+' '+msl+' : '+warps+' '+note1+' '+note2);
      2: s_sum:=trimright(sector+' '+port1+' '+gate1+'/'+gate2+' : '+warps+' '+note1+' '+note2);
      3: s_sum:=trimright(sector+' '+port1+' '+port2+' '+port3+' '+gate1+'/'+gate2+' '+msl+' : '+warps+' '+note1+' '+note2);
      4: s_sum:=trimright(sector+' '+port1+' '+gate2+' '+msl+' '+sol+' : '+warps+' '+note1+' '+note2);
      otherwise s_sum:='';
    end;

  end; { else }

end;
{
procedure b_sum(i: word; ps: pointer; fp: pointer; ns, mw: word; lns: byte);
var
  fhandle: ^text;
  s: ^tsector;
  j: word;
begin
  fhandle:=fp;
  s:=ps;
  if not(s[i-1].bu=nil) then
  begin
    writeln(fhandle^,' >',s_sum(s[i-1].bu^.bid,s,mw,lns,0));
    for j:=1 to ns do
      if not(s[j-1].bu=nil) then
        if (s[j-1].bu^.bid=s[i-1].bu^.bid) and not(j=s[i-1].bu^.bid) then writeln(fhandle^,'  ',s_sum(j,s,mw,lns,0));
  end;
end;
}
procedure bubbleanalysis(ps: pointer; ns, mw: word; fname: ansistring);
var
  s: ^tsector;
  fhandle: text;
  sectorheader: ansistring;
  a, c, d, i, j, k, n, gate, mon: word;
  lns: byte;
  flag1, flag2, flag3, flag4, flag5, done: boolean;
  fgate: ^boolean;
  b : ^word;
begin
  s:=ps;
  getmem(b,ns*sizeof(word));
  getmem(fgate,ns*sizeof(boolean));

  lns:=floor(log10(ns))+1;

  sectorheader:=s_sum(0,s,mw,lns,4);

  if length(fname)>33 then write('writing bubble report: ...',rightstr(fname,30),' ')
  else write('writing bubble report: ',fname,' ');
  assign(fhandle,fname);
  rewrite(fhandle);

  writeln(fhandle,'key: >    - the bubble gate is identified with a ">" on the left.');
  writeln(fhandle,'     u    - some sectors in, or one-ways out of, the bubble are unexplored.');
  writeln(fhandle,'     c    - the bubble is compromised by one-way warps in.');
  writeln(fhandle,'     d    - distance from bottom of bubble.');
  writeln(fhandle,'     ()   - the sector is unexplored.');
  writeln(fhandle,'     []   - the port in that sector is not reporting.');
  writeln(fhandle,'     +    - the sector has a fig deployed.');
  writeln(fhandle,'note:  sector warps to the right may include oneways in, not seen in sector.');

  mon:=spinner(0,1000);

  // identify 1-deeps
  for i:=1 to ns do
    b[i-1]:=0;

  write('0');
  n:=1;
  for i:=1 to ns do
    with s[i-1] do
    begin
      mon:=spinner(mon,1000);
      c:=0;
      flag1:=true; // bubble explored
      if not(wp=nil) then
        for j:=1 to wp^.nw do
          if s[wp^.warps[j-1]-1].wp=nil then
            writeln(fhandle,'*** reconciliation error between sectors ',i,' and ',wp^.warps[j-1],'.')
          else
          begin
            if not(s[wp^.warps[j-1]-1].v) and not(wp^.warptype[j-1]=w_in) then
              flag1:=false; // bubble not explored
            if wp^.warptype[j-1]=w_both then
            begin
              c+=1;
              gate:=wp^.warps[j-1];
            end;
          end;
      if c=1 then
      begin
        if not(bu=nil) then freemem(bu);
        getmem(bu,sizeof(tbubble));
        bu^.depth:=1;
        bu^.comp:=(wp^.nwi>0);
        bu^.expl:=(v and flag1);
        bu^.bid:=gate;
        b[gate-1]:=i
      end;
    end;

  // report output
{ flag1:=true;
  for i:=1 to ns do
  begin
    mon:=spinner(mon,1000);
    if not(b[i-1]=0) then
    begin
      if flag1 then
      begin
        writeln(fhandle,' ',n,'-deeps:');
        writeln(fhandle,'  ',sectorheader);
        flag1:=false;
      end;
      b_sum(b[i-1],s,@fhandle,ns,mw,lns);
    end;
  end;
}
  // identify n-deeps
  done:=false;
  n:=2;
  while not(done) do
  begin
    write((n-1) mod 10);
    for i:=1 to ns do
      b[i-1]:=0;
    done:=true;
    for i:=1 to ns do
      with s[i-1] do
      begin
        mon:=spinner(mon,1000);
        if bu=nil then
        begin
          c:=0;
          flag1:=true; // bubble explored
          flag2:=false; // bubble not compromised
          if not(wp=nil) then
            for j:=1 to wp^.nw do
              if s[wp^.warps[j-1]-1].wp=nil then
                writeln(fhandle,'*** reconciliation error between sectors ',i,' and ',wp^.warps[j-1],'.')
              else
              begin
                if (s[wp^.warps[j-1]-1].wp^.nwi>0) and not(wp^.warptype[j-1]=w_out) then
                  flag2:=true;
                flag3:=not(s[wp^.warps[j-1]-1].bu=nil); // connecting warp a bubble?
                if flag3 then
                begin
                  flag4:=(s[wp^.warps[j-1]-1].bu^.depth=n); // connecting bubble depth=n?
                  flag5:=s[wp^.warps[j-1]-1].bu^.expl; // connecting bubble explored?
                end
                else
                begin
                  flag4:=false; // connecting bubble depth=n?
                  flag5:=false; // connecting bubble explored?
                end;
                if ((wp^.warptype[j-1]=w_both) and not(flag3)) or ((wp^.warptype[j-1]=w_both) and flag4) then
                begin
                  c+=1;
                  gate:=wp^.warps[j-1];
                end
                else if not(flag5) and (wp^.warptype[j-1]=w_both) then flag1:=false;
                if not(s[wp^.warps[j-1]-1].v) then flag1:=false;
              end;
          if c=1 then
          begin
            done:=false;
            if not(bu=nil) then freemem(bu);
            getmem(bu,sizeof(tbubble));
            bu^.depth:=n;
            bu^.comp:=(wp^.nwi>0) or flag2;
            bu^.expl:=flag1;
            bu^.bid:=gate;
            for j:=1 to wp^.nw do
              if not(wp^.warps[j-1]=gate) and not(wp^.warptype[j-1]=w_out) then
                for k:=1 to ns do
                  if not (s[k-1].bu=nil) then
                    if (s[k-1].bu^.bid=i) then s[k-1].bu^.bid:=gate;
            b[gate-1]:=i;
          end;
        end;
      end;

    // report output
{   flag1:=true;
    for i:=1 to ns do
    begin
      mon:=spinner(mon,1000);
      if not(b[i-1]=0) then
      begin
        if flag1 then
        begin
          writeln(fhandle,n,'-deeps:');
          writeln(fhandle,'  ',sectorheader);
          flag1:=false;
        end;
        b_sum(b[i-1],s,@fhandle,ns,mw,lns);
      end;
    end;
}
    n+=1;
  end;
  n-=1;

  // create boolean array of all gates
  for i:=1 to ns do
    fgate[i-1]:=false;
  for i:=1 to ns do
    if not(s[i-1].bu=nil) then
      fgate[s[i-1].bu^.bid-1]:=true;

  // create report
  for i:=n downto 1 do
  begin
    flag1:=true;
    for j:=1 to ns do
    begin
      if fgate[j-1] and not(s[j-1].wp=nil) then
      begin
        d:=0;
        for k:=1 to s[j-1].wp^.nw do
        begin
          a:=s[j-1].wp^.warps[k-1];
          if not(s[a-1].wp=nil) and not(s[a-1].bu=nil) then
            if s[a-1].bu^.bid=j then d:=max(d,s[a-1].bu^.depth)
        end;
        if d=i then
        begin
          if flag1 then
          begin
            writeln(fhandle,i,'-DEEP BUBBLES:');
            writeln(fhandle,'  ',sectorheader);
            flag1:=false;
          end;
          fgate[j-1]:=false;
          writeln(fhandle,' >',s_sum(j,s,mw,lns,4));
          for k:=1 to ns do
            if not(s[k-1].bu=nil) then
              if (s[k-1].bu^.bid=j) and not(k=j) then writeln(fhandle,'  ',s_sum(k,s,mw,lns,4));
        end;
      end;
      mon:=spinner(mon,1000);
    end;
  end;

  if not(b=nil) then freemem(b);
  if not(fgate=nil) then freemem(fgate);
  close(fhandle);
  writeln('.');
end;

procedure blockedports(ps: pointer; ns: word; fname: ansistring);
var
  s: ^tsector;
  fhandle: text;
  i, n, mon: word;
  line, macro: ansistring;
begin
  s:=ps;
  assign(fhandle,fname);
  rewrite(fhandle);
  if length(fname)>33 then write('writing blocked port report: ...',rightstr(fname,30),' ')
  else write('writing blocked port report: ',fname,' ');
  mon:=spinner(0,500);

  writeln(fhandle,'key: *=port in bubble');
  writeln(fhandle,'blocked ports:');
  line:='';
  macro:='';
  n:=0;
  for i:=1 to ns do
    with s[i-1] do
    begin
      mon:=spinner(mon,1000);
      if not(pt=nil) and v then
        if not(pt^.v) then
        begin
          macro:=macro+'s'+inttostr(i)+';';

          line:=line+stringofchar(' ',6-length(inttostr(i)));
          if (s[i-1].figs) then line:=line+'+'
                           else line:=line+' ';
          line:=line+inttostr(i)+'('+portstr(i,3001,s)+')';
          if not(bu=nil) then line:=line+'*'
                         else line:=line+' ';
          n+=1;
          if (n mod 6)=0 then
          begin
            writeln(fhandle,line);
            line:='';
          end;
        end;
    end;
  if length(line)>0 then writeln(fhandle,line);

  writeln(fhandle,'unexplored ports:');
  line:='';
  n:=0;
  for i:=1 to ns do
    with s[i-1] do
    begin
      mon:=spinner(mon,1000);
      if not(pt=nil) and not(v) then
      begin
        line:=line+stringofchar(' ',6-length(inttostr(i)));
        if (s[i-1].figs) then line:=line+'+'
                         else line:=line+' ';
        line:=line+inttostr(i)+'('+portstr(i,3001,s)+')';
        if not(bu=nil) then line:=line+'*'
                       else line:=line+' ';
        n+=1;
        if (n mod 6)=0 then
        begin
          writeln(fhandle,line);
          line:='';
        end;
      end;
    end;
  if length(line)>0 then writeln(fhandle,line);

  writeln(fhandle,'void blocked ports macro:');
  for i:=1 to wordcount(macro,';') do
    writeln(fhandle,wordget(macro,i,';'));

  writeln('.');
  close(fhandle);
end;

procedure oneways(ps: pointer; ns: word; fname: ansistring);
var
  s: ^tsector;
  fhandle: text;
  i, j, l, n, mon: word;
  line, str1: ansistring;
begin
  s:=ps;
  assign(fhandle,fname);
  rewrite(fhandle);
  if length(fname)>33 then write('writing one-way report: ...',rightstr(fname,30),' ')
  else write('writing one-way report: ',fname,' ');
  mon:=spinner(0,1000);
  l:=floor(log10(ns))+1;

  writeln(fhandle,'oneways out:');
  line:='';
  n:=0;
  for i:=1 to ns do
    with s[i-1] do
    begin
      mon:=spinner(mon,1000);
      if not(wp=nil) then
        for j:=1 to wp^.nw do
        begin
          if wp^.warptype[j-1]=w_out then
          begin
            str1:=inttostr(i);
            line:=line+stringofchar(' ',l-length(str1))+str1+'-->';
            str1:=inttostr(wp^.warps[j-1]);
            line:=line+str1+stringofchar(' ',l-length(str1))+'  ';
            n+=1;
          end;
          if n=5 then
          begin
            writeln(fhandle,' ',trimright(line));
            line:='';
            n:=0;
          end;
        end;
    end;
  if not(line='') then writeln(fhandle,' ',trimright(line));
  writeln(fhandle);

  writeln(fhandle,'oneways in:');
  line:='';
  n:=0;
  for i:=1 to ns do
    with s[i-1] do
    begin
      mon:=spinner(mon,1000);
      if not(wp=nil) then
        for j:=1 to wp^.nw do
        begin
          if wp^.warptype[j-1]=w_out then
          begin
            str1:=inttostr(i);
            line:=line+stringofchar(' ',l-length(str1))+str1+'<--';
            str1:=inttostr(wp^.warps[j-1]);
            line:=line+str1+stringofchar(' ',l-length(str1))+'  ';
            n+=1;
          end;
          if n=5 then
          begin
            writeln(fhandle,' ',trimright(line));
            line:='';
            n:=0;
          end;
        end;
    end;
  if not(line='') then writeln(fhandle,' ',trimright(line));

  close(fhandle);
  writeln('.');
end;

procedure secfind(b, i: word; ps, pf: pointer);
var
  s: ^tsector;
  f: ^boolean;
  j: word;
begin
  s:=ps;
  f:=pf;
  f[i-1]:=true;
  with s[i-1] do
    if not(wp=nil) then
      for j:=1 to wp^.nw do
        if wp^.warptype[j-1]<=w_both then
          if not(f[wp^.warps[j-1]-1] or (wp^.warps[j-1]=b)) then secfind(b,wp^.warps[j-1],s,f);
end;

procedure secludedanalysis(ps: pointer; ns, mw: word; fname: ansistring);
var
  s: ^tsector;
  f, g: ^boolean;
  fhandle: text;
  sectorheader: ansistring;
  c, i, j, k, n, lns, mon: word;
  done, flag1, flag2: boolean;
begin
  s:=ps;
  getmem(f,ns*sizeof(boolean));
  getmem(g,ns*sizeof(boolean));

  lns:=floor(log10(ns))+1;

  sectorheader:=s_sum(0,s,mw,lns,1);

  if length(fname)>33 then write('writing secluded report: ...',rightstr(fname,30),' ')
  else write('writing secluded report: ',fname,' ');
  assign(fhandle,fname);
  rewrite(fhandle);

  writeln(fhandle,'key: >    - the secluded gate is identified with a ">" on the left.');
  writeln(fhandle,'     gate - the gate of a bubble within the secluded area.');
  writeln(fhandle,'     u    - some sectors in, or one-ways out of, the bubble are unexplored.');
  writeln(fhandle,'     c    - the bubble is compromised by one-way warps in.');
  writeln(fhandle,'     d    - distance from bottom of bubble.');
  writeln(fhandle,'     ()   - the sector is unexplored.');
  writeln(fhandle,'     []   - the port in that sector is not reporting.');
  writeln(fhandle,'note:  sector warps to the right include oneways in, not seen in sector.');

  mon:=spinner(0,100);

  for i:=1 to ns do
    g[i-1]:=false;

  for i:=1 to ns do
    if not(s[i-1].bu=nil) then g[s[i-1].bu^.bid-1]:=true;

  for i:=2 to ns do
    with s[i-1] do
    begin
      mon:=spinner(mon,100);
      if (bu=nil) and not(g[i-1]) then
      begin
        for j:=1 to ns do
          f[j-1]:=false;
        secfind(i,1,s,f);
        // search for secludeds within secludeds
        k:=0;
        n:=i;
        for j:=1 to ns do
        begin
          if not(s[j-1].sid=nil) then flag2:=(s[j-1].sid^=n)
          else flag2:=false;
          if not(f[j-1]) and not(s[j-1].wp=nil) and not(flag2) then
          begin
           if not(sid=nil) then n:=s[j-1].sid^
           else n:=0;
           k+=1;
          end;
        end;
        // if multiple secludeds inside current secluded, then assign new # for entire area
        if (k>1) or ((k=1) and (n=0)) then
          for j:=1 to ns do
            if not(f[j-1]) and not(s[j-1].wp=nil) and not(i=j) then
            begin
              if s[j-1].sid=nil then getmem(s[j-1].sid,sizeof(word));
              s[j-1].sid^:=i;
            end;
      end;
    end;

  writeln(fhandle,' ',sectorheader);
  n:=0;
  j:=ns; // min
  k:=1;  // max
  for i:=1 to ns do
    with s[i-1] do
    begin
      if not(sid=nil) then
      begin
        if sid^<j then j:=sid^;
        if sid^>k then k:=sid^;
      end;
    end;

  n:=j;
  done:=false;
  while not(done) do
  begin
    flag1:=false;
    for i:=1 to ns do
      with s[i-1] do
        if not(sid=nil) then
        begin
          mon:=spinner(mon,100);
          if not(bu=nil) then flag2:=(bu^.bid=sid^)
          else flag2:=false;
          if (sid^=n) and not((flag2) or (i=sid^)) then
          begin
            flag1:=true;
            break;
          end;
        end;
    if flag1 then writeln(fhandle,'>',s_sum(n,s,mw,lns,1));
    c:=k;
    for i:=1 to ns do
      with s[i-1] do
        if not(sid=nil) then
        begin
          mon:=spinner(mon,100);
          if (sid^=n) and flag1 then writeln(fhandle,' ',s_sum(i,s,mw,lns,1));
          if (sid^>n) and (sid^<c) and (sid^>0) then c:=sid^;
        end;
    if n=c then done:=true;
    n:=c;
  end;

  close(fhandle);
  freemem(f);
  freemem(g);
  writeln('.');
end;

procedure distcalc(ps: pointer; ns: word; pdlist: pointer; dcount: word);
var
  s: ^tsector;
  dlist: ^word;
  i, j, k, n: word;
  done: boolean;
begin
  s:=ps; dlist:=pdlist;

  write('calculating distances to special sectors: ');
  for k:=2 to dcount do
    if dlist[k-1]>0 then
      with s[dlist[k-1]-1] do
      begin
        ds_to[k-1]:=0;
        ds_from[k-1]:=0;
        if not(wp=nil) then
        begin
          for j:=1 to wp^.nw do
          begin
            if wp^.warptype[j-1]<=w_both then
              s[wp^.warps[j-1]-1].ds_from[k-1]:=1; // i.e. distance from alpha to x
            if wp^.warptype[j-1]>=w_both then
              s[wp^.warps[j-1]-1].ds_to[k-1]:=1; // i.e. distance from x to alpha
          end;

          // ds_from
          done:=false;
          n:=1;
          while not(done) do
          begin
            done:=true;
            for i:=1 to ns do
              if s[i-1].ds_from[k-1]=n then
                if not(s[i-1].wp=nil) then
                  for j:=1 to s[i-1].wp^.nw do
                    if (s[s[i-1].wp^.warps[j-1]-1].ds_from[k-1]=255) and (s[i-1].wp^.warptype[j-1]<=w_both) then
                    begin
                      done:=false;
                      s[s[i-1].wp^.warps[j-1]-1].ds_from[k-1]:=n+1;
                    end;
            n+=1;
          end;

          // ds_to
          done:=false;
          n:=1;
          while not(done) do
          begin
            done:=true;
            for i:=1 to ns do
              if s[i-1].ds_to[k-1]=n then
                if not(s[i-1].wp=nil) then
                  for j:=1 to s[i-1].wp^.nw do
                    if (s[s[i-1].wp^.warps[j-1]-1].ds_to[k-1]=255) and (s[i-1].wp^.warptype[j-1]>=w_both) then
                    begin
                      done:=false;
                      s[s[i-1].wp^.warps[j-1]-1].ds_to[k-1]:=n+1;
                    end;
            n+=1;
          end;
        end;
      end;

  writeln('.');
end;

procedure distancereport(ps: pointer; ns: word; pdlist: pointer; dcount: word; fname: ansistring);
var
  s: ^tsector;
  dlist: ^word;
  fhandle: text;
  i, j, l: word;
  str1: ansistring;
  line1, line2: ansistring;
begin
  s:=ps; dlist:=pdlist;
  if length(fname)>33 then write('writing distance report: ...',rightstr(fname,30),' ')
  else write('writing distance report: ',fname,' ');
  l:=floor(log10(ns))+1;
  assign(fhandle,fname);
  rewrite(fhandle);

  writeln(fhandle,stringofchar(' ',l-2),'A  |  B..->  (from A to B),(from B to A)');
  line2:=stringofchar('-',l+1)+'+';
  for j:=1 to dcount do
    line2:=line2+'-------+';
  writeln(fhandle,line2);
  write(fhandle,leftstr('sector ',l+1),'|  msl  | terra | alpha | rylos | strdk |');
  for j:=6 to dcount do
    write(fhandle,'       |');
  writeln(fhandle);
  write(fhandle,stringofchar(' ',l+1),'|       |');
  line1:='';
  for j:=2 to dcount do
  begin
    str1:=inttostr(dlist[j-1]);
    line1:=line1+stringofchar(' ',(7-length(str1)) div 2 + (7-length(str1)) mod 2)+str1+stringofchar(' ',(7-length(str1)) div 2)+'|';
  end;
  writeln(fhandle,line1);
  writeln(fhandle,line2);
  line1:=leftstr('sector ',l+1)+'|  msl  |'+line1;

  for j:=1 to ns do
  begin
    str1:=inttostr(j);
    write(fhandle,stringofchar(' ',l-length(str1)),str1,' |');
    for i:=1 to dcount do
    begin
      str1:=inttostr(s[j-1].ds_to[i-1]);
      write(fhandle,stringofchar(' ',3-length(str1)),str1,',');
      str1:=inttostr(s[j-1].ds_from[i-1]);
      write(fhandle,str1,stringofchar(' ',3-length(str1)),'|');
    end;
    writeln(fhandle);
    if (j mod 25)=0 then
    begin
      writeln(fhandle,line2);
      writeln(fhandle,line1);
      writeln(fhandle,line2);
    end;
  end;
  close(fhandle);
  writeln('.');
end;

procedure mslcalc(ps: pointer; ns: word; pdlist: pointer; dcount: word; fname: ansistring);
var
  s: ^tsector;
  dlist: ^word;
  mind, i, j, l, n, current, start, finish: word;
  flag1, done: boolean;
  str1: ansistring;
  a_strings: array [0..7] of ansistring;
  fhandle: text;
const
  a_from: array[0..7] of byte =(1,4,2,3,2,4,3,4);
  a_to:   array[0..7] of byte =(4,1,3,2,4,2,4,3);
begin
  s:=ps; dlist:=pdlist;

  flag1:=true;
  for i:=2 to dcount do
    if dlist[i-1]=0 then flag1:=false;

  if flag1 then
  begin
    write('calculating msl: ');
    // 0 terra to dock
    // 1 dock to terra
    // 2 alpha to rylos
    // 3 rylos to alpha
    // 4 alpha to dock
    // 5 dock to alpha
    // 6 rylos to dock
    // 7 dock to rylos
    for i:=0 to 7 do
    begin
      start:=dlist[a_from[i]];
      finish:=dlist[a_to[i]];
      current:=start;
      done:=false;
      a_strings[i]:=inttostr(start);
      s[start-1].ds_to[0]:=0;
      s[start-1].ds_from[0]:=0;
      mind:=s[start-1].ds_to[a_to[i]];
      while not(done) do
        with s[current-1] do
        begin
          if not(wp=nil) then
          begin
            done:=true;
            for j:=1 to wp^.nw do
              if (wp^.warptype[j-1]<=w_both) and (s[wp^.warps[j-1]-1].ds_to[a_to[i]]<mind) then
              begin
                mind:=s[wp^.warps[j-1]-1].ds_to[a_to[i]];
                current:=wp^.warps[j-1];
                a_strings[i]:=a_strings[i]+' > '+inttostr(current);
                s[current-1].ds_to[0]:=0;
                s[current-1].ds_from[0]:=0;
                done:=false;
                break;
              end
          end
          else done:=true;
          if current=finish then done:=true;
        end;
    end;
    writeln('.');
    if length(fname)>33 then write('writing msl report: ...',rightstr(fname,30),' ')
    else write('writing msl report: ',fname,' ');

    assign(fhandle,fname);
    rewrite(fhandle);
    l:=floor(log10(ns))+1;
    for i:=0 to 7 do
    begin
      case i of
        0: writeln(fhandle,stringofchar(' ',l*2+6),'terra to stardock');
        1: writeln(fhandle,stringofchar(' ',l*2+6),'stardock to terra');
        2: writeln(fhandle,stringofchar(' ',l*2+6),'alpha centauri to rylos');
        3: writeln(fhandle,stringofchar(' ',l*2+6),'rylos to alpha centauri');
        4: writeln(fhandle,stringofchar(' ',l*2+6),'alpha centauri to stardock');
        5: writeln(fhandle,stringofchar(' ',l*2+6),'stardock to alpha centauri');
        6: writeln(fhandle,stringofchar(' ',l*2+6),'rylos to stardock');
        7: writeln(fhandle,stringofchar(' ',l*2+6),'stardock to rylos');
      end;
      str1:=inttostr(dlist[a_from[i]]);
      write(fhandle,stringofchar(' ',l-length(str1)),str1,'-->');
      str1:=inttostr(dlist[a_to[i]]);
      write(fhandle,str1,stringofchar(' ',l-length(str1)));
      writeln(fhandle,' : ',a_strings[i]);
      writeln(fhandle);
    end;

    // ds_from
    done:=false;
    n:=0;
    while not(done) do
    begin
      done:=true;
      for i:=1 to ns do
        if s[i-1].ds_from[0]=n then
          if not(s[i-1].wp=nil) then
            for j:=1 to s[i-1].wp^.nw do
              if (s[s[i-1].wp^.warps[j-1]-1].ds_from[0]=255) and (s[i-1].wp^.warptype[j-1]<=w_both) then
              begin
                done:=false;
                s[s[i-1].wp^.warps[j-1]-1].ds_from[0]:=n+1;
              end;
      n+=1;
    end;

    // ds_to
    done:=false;
    n:=0;
    while not(done) do
    begin
      done:=true;
      for i:=1 to ns do
        if s[i-1].ds_to[0]=n then
          if not(s[i-1].wp=nil) then
            for j:=1 to s[i-1].wp^.nw do
              if (s[s[i-1].wp^.warps[j-1]-1].ds_to[0]=255) and (s[i-1].wp^.warptype[j-1]>=w_both) then
              begin
                done:=false;
                s[s[i-1].wp^.warps[j-1]-1].ds_to[0]:=n+1;
              end;
      n+=1;
    end;

    writeln(fhandle,'amtrak sectors around fed');
    for i:=1 to 10 do
      if not(s[i-1].wp=nil) then
      begin
        str1:=inttostr(i);
        write(fhandle,stringofchar(' ',l-length(str1)),str1,' : ');
        for j:=1 to s[i-1].wp^.nw do
          if (s[i-1].wp^.warptype[j-1]<=w_both) and (s[i-1].wp^.warps[j-1]>10) and not(s[s[i-1].wp^.warps[j-1]-1].ds_from[0]=0) then
          begin
            if s[s[i-1].wp^.warps[j-1]-1].figs then write(fhandle,'+');
            write(fhandle,s[i-1].wp^.warps[j-1],' ');
          end;
        writeln(fhandle);
      end;
    writeln(fhandle,'amtrak sectors around msl');
    for i:=11 to ns do
      if not(s[i-1].wp=nil) and (s[i-1].ds_from[0]=0) then
      begin
        str1:=inttostr(i);
        write(fhandle,stringofchar(' ',l-length(str1)),str1,' : ');
        for j:=1 to s[i-1].wp^.nw do
          if (s[i-1].wp^.warptype[j-1]<=w_both) and (s[i-1].wp^.warps[j-1]>10) and not(s[s[i-1].wp^.warps[j-1]-1].ds_from[0]=0) then
          begin
            if s[s[i-1].wp^.warps[j-1]-1].figs then write(fhandle,'+');
            write(fhandle,s[i-1].wp^.warps[j-1],' ');
          end;
        writeln(fhandle);
      end;

    close(fhandle);
    writeln('.');

  end;
end;

procedure specialportreport(ps: pointer; ns, mw: word; fname: ansistring);
var
  s: ^tsector;
  f: ^boolean;
  fhandle: text;
  d, i, j, l: word;
  flag1, flag2: boolean;
  sectorheader: ansistring;
begin
  s:=ps;
  if length(fname)>33 then write('writing special port report: ...',rightstr(fname,30),' ')
  else write('writing special port report: ',fname,' ');
  getmem(f,ns*sizeof(boolean));
  assign(fhandle,fname);
  rewrite(fhandle);
  l:=floor(log10(ns))+1;
  sectorheader:=s_sum(0,s,mw,l,2);
  writeln(fhandle,'special port report');
  d:=0;
  for i:=1 to ns do // flag sectors with 6 warps out and at least 7 warps in
  begin
    f[i-1]:=false;
    if not(s[i-1].wp=nil) then
    begin
      if (s[i-1].wp^.nw>=7) and (s[i-1].wp^.nwi>=1) then
        f[i-1]:=true;
      d:=max(d,s[i-1].ds_from[1]);
    end;
  end;
  for j:=1 to d do
  begin
    flag1:=true;
    for i:=1 to ns do
    begin
      flag2:=false;
      if s[i-1].pt=nil then flag2:=true                             // no port could be class 0
                       else if s[i-1].pt^.ptype=7 then flag2:=true; // BBB port could be stardock
      if f[i-1] and (s[i-1].ds_from[1]=j) and flag2 then
      begin
        if flag1 then writeln(fhandle,j,' hops from terra');
        if flag1 then writeln(fhandle,' ',sectorheader);
        flag1:=false;
        writeln(fhandle,' ',s_sum(i,s,mw,l,2));
      end;
    end;
  end;
  close(fhandle);
  freemem(f);
  writeln('.');
end;

procedure deadends(ps: pointer; ns, mw: word; fname: ansistring);
var
  s: ^tsector;
  fhandle: text;
  i, j, k, n, d, a, lns, mon: word;
  fgate: ^boolean;
  b : ^word;
  flag1: boolean;
  sectorheader: ansistring;
begin
  s:=ps;
  mon:=0;
  getmem(b,ns*sizeof(word));
  getmem(fgate,ns*sizeof(boolean));
  assign(fhandle,fname);
  rewrite(fhandle);
  if length(fname)>33 then write('writing deadend report: ...',rightstr(fname,30),' ')
  else write('writing deadend report: ',fname,' ');
  writeln(fhandle,'blocked deadends:');
  lns:=floor(log10(ns))+1;
  for i:=1 to ns do
    with s[i-1] do
      if not(bu=nil) and v and not(pt=nil) then
        if (bu^.depth=1) and not(pt^.v) then writeln(fhandle,' ',s_sum(i,s,mw,lns,1));
  writeln(fhandle,'port deadends:');
  for i:=1 to ns do
    with s[i-1] do
      if not(bu=nil) and v and not(pt=nil) then
        if (bu^.depth=1) and pt^.v then writeln(fhandle,' ',s_sum(i,s,mw,lns,1));
  writeln(fhandle,'portless deadends:');
  for i:=1 to ns do
    with s[i-1] do
      if not(bu=nil) and v and (pt=nil) then
        if bu^.depth=1 then writeln(fhandle,' ',s_sum(i,s,mw,lns,1));
  writeln(fhandle,'unexplored deadends:');
  for i:=1 to ns do
    with s[i-1] do
      if not(bu=nil) and not(v) then
        if bu^.depth=1 then writeln(fhandle,' ',s_sum(i,s,mw,lns,1));
  writeln(fhandle,'all deadends:');
  for i:=1 to ns do
    with s[i-1] do
      if not(bu=nil) then
        if bu^.depth=1 then writeln(fhandle,' ',s_sum(i,s,mw,lns,1));

  writeln(fhandle,'bubbles with blocked ports:');
  sectorheader:=s_sum(0,s,mw,lns,0);

  // create boolean array of all gates
  for i:=1 to ns do
    fgate[i-1]:=false;
  for i:=1 to ns do
    if not(s[i-1].bu=nil) and not(s[i-1].pt=nil) then
      if not(s[i-1].pt^.v) then
        fgate[s[i-1].bu^.bid-1]:=true;

  // find max bubble depth
  n:=1;
  for i:=1 to ns do
    if not(s[i-1].bu=nil) then
      n:=max(n,s[i-1].bu^.depth);

  // create report
  for i:=n downto 1 do
  begin
    flag1:=true;
    for j:=1 to ns do
    begin
      if fgate[j-1] and not(s[j-1].wp=nil) then
      begin
        d:=0;
        for k:=1 to s[j-1].wp^.nw do
        begin
          a:=s[j-1].wp^.warps[k-1];
          if not(s[a-1].wp=nil) and not(s[a-1].bu=nil) then
            d:=max(d,s[a-1].bu^.depth)
        end;
        if d=i then
        begin
          if flag1 then
          begin
            writeln(fhandle,i,'-DEEP BUBBLES:');
            writeln(fhandle,'  ',sectorheader);
            flag1:=false;
          end;
          fgate[j-1]:=false;
          writeln(fhandle,' >',s_sum(j,s,mw,lns,0));
          for k:=1 to ns do
            if not(s[k-1].bu=nil) then
              if (s[k-1].bu^.bid=j) and not(k=j) then writeln(fhandle,'  ',s_sum(k,s,mw,lns,0));
        end;
      end;
      mon:=spinner(mon,1000);
    end;
  end;

  if not(b=nil) then freemem(b);
  if not(fgate=nil) then freemem(fgate);

  close(fhandle);
  writeln('.');
end;

procedure dumpreport(ps:pointer; ns, mw: word; fname:ansistring);
var
  s: ^tsector;
  i, l: word;
  fhandle: text;
begin
  s:=ps;
  assign(fhandle,fname);
  rewrite(fhandle);
  if length(fname)>33 then write('writing dump report: ...',rightstr(fname,30),' ')
  else write('writing dump report: ',fname,' ');

  l:=floor(log10(ns))+1;
  writeln(fhandle,s_sum(0,s,mw,l,3));

  for i:=1 to ns do
    writeln(fhandle,s_sum(i,s,mw,l,3));

  close(fhandle);
  writeln('.');
end;

procedure readfigs(ps: pointer; ns: word; fname: ansistring; plhandle: pointer);
var
  s: ^tsector;
  lhandle: ^text;
  fhandle: text;
  line: ansistring;
  c, mon, snum: word;
begin
  s:=ps;
  lhandle:=plhandle;
  if fileexists(fname) then
  begin
    write(lhandle^,' ',fname,': ');
    assign(fhandle,fname);
    reset(fhandle);
    if length(fname)>33 then write('reading fig data: ',rightstr(fname,30),' ')
    else write('reading fig data: ',fname,' ');
    mon:=spinner(0,100);
    c:=0;
    while not(eof(fhandle)) do
    begin
      readln(fhandle,line);
      try
        snum:=strtoint(line);
      except
        on E : EConvertError do snum:=0;
      end;
      if (snum>0) and (snum<=ns) then
      begin
        s[snum-1].figs:=true;
        c+=1;
        mon:=spinner(mon,100);
      end;
    end;
    close(fhandle);
    writeln('.');
    writeln(lhandle^,c,' sectors read.');
  end;
end;

procedure onewaytunnels(ps: pointer; ns: word; fname: ansistring);
var
  s: ^tsector;
  i, j, k, c1, c2: word;
  f: ^boolean;
  fhandle: text;
begin
  s:=ps;
  assign(fhandle,fname);
  rewrite(fhandle);
  writeln(fhandle,'one-way tunnel report');
  if length(fname)>33 then write('writing one-way tunnel report: ...',rightstr(fname,30),' ')
  else write('writing one-way tunnel report: ',fname,' ');
  getmem(f,ns*sizeof(boolean));
  for i:=1 to ns do
    with s[i-1] do
    begin
      f[i-1]:=false;
      if not(wp=nil) then
      begin
        c1:=0; c2:=0;
        for j:=1 to wp^.nw do
        begin
          if wp^.warptype[j-1]=w_in then c1+=1;
          if wp^.warptype[j-1]=w_out then c2+=1;
        end;
        if (c1=1) and (c2=1) and (wp^.nw=2) then
        begin
          f[i-1]:=true;
        end;
      end;
    end;
  for i:=1 to ns do
    with s[i-1] do
      if f[i-1] then
        for j:=1 to ns do
          if f[j-1] and (j>i) then
            for k:=1 to wp^.nw do
              if wp^.warps[k-1]=j then writeln(fhandle,i,',',j,' ');
  writeln('.');
  close(fhandle);
  freemem(f);
end;

procedure writemap(ps: pointer; ns: word; fname: ansistring);
var
  s: ^tsector;
  fhandle: text;
  num1, nwmax: word;
  i, j: word;
  k: tproducts;
begin
{
            MAP FORMAT
F QQ P QQ P QQ P MM BG I W1 W2 .. Wn

one letter=byte
two letters=word

F  - 0 - expl?
     1 - one-deep?
     2 - (unused)
     3 - port?
     4 - portvis?
     5\
     6 > ptype
     7/
QQ - product quantity
P  - product percent
MM - distances from msl
BG - bubble gate
I  - number of oneways in
W1 - warps 1..n

reclen=15+2n
}
  s:=ps;
  assign(fhandle,fname);
  rewrite(fhandle);
  nwmax:=0;
  for i:=1 to ns do
    if not(s[i-1].wp=nil) then nwmax:=max(nwmax,s[i-1].wp^.nw);
  if length(fname)>33 then write('writing map (reclen=',15+2*nwmax,'): ',rightstr(fname,30),' ')
  else write('writing map (reclen=',15+2*nwmax,'): ',fname,' ');
  write(fhandle,char(15+2*nwmax));
  for i:=1 to ns do
    with s[i-1] do
    begin
      // write F
      num1:=0;
      if v then num1:=num1+(1 shl 0);
      if not(bu=nil) then
        if bu^.depth=1 then num1:=num1+(1 shl 1);
      if not(pt=nil) then
      begin
        num1:=num1+(1 shl 3);
        if pt^.v then num1:=num1+(1 shl 4);
        num1:=num1+(pt^.ptype shl 5);
      end;
      write(fhandle,char(num1));

      // write QQ P QQ P QQ P
      if pt=nil then write(fhandle,stringofchar(char(0),9))
      else
        for k:=ore to equ do
        begin
          write(fhandle,char(pt^.quantity[k] mod 256));
          write(fhandle,char(pt^.quantity[k] div 256));
          write(fhandle,char(pt^.percent[k]));
        end;

      // write MM
      write(fhandle,char(ds_to[0]));
      write(fhandle,char(ds_from[0]));

      // write BG
      if bu=nil then write(fhandle,stringofchar(char(0),2))
      else
      begin
        write(fhandle,char(bu^.bid mod 256));
        write(fhandle,char(bu^.bid div 256));
      end;

      // write I
      if wp=nil then write(fhandle,char(0))
      else write(fhandle,char(wp^.nwi));

      // write W1 .. Wn
      for j:=1 to nwmax do
        if wp=nil then write(fhandle,stringofchar(char(0),2))
        else
          if j>wp^.nw then write(fhandle,stringofchar(char(0),2))
          else
          begin
            case wp^.warptype[j-1] of
              w_out : num1:=wp^.warps[j-1];
              w_both: num1:=wp^.warps[j-1]+20000;
              w_in  : num1:=wp^.warps[j-1]+40000;
            end;
            write(fhandle,char(num1 mod 256));
            write(fhandle,char(num1 div 256));
          end;
    end;
  close(fhandle);
  writeln('.');
end;

procedure readlog(ps: pointer; ns: word; fname: ansistring);
var
  s: ^tsector;
  fhandle: text;
  line: ansistring;
  i: word;
begin
  s:=ps;
  if fileexists(fname) then
  begin
    if length(fname)>33 then write('reading log: ...',rightstr(fname,30),' ')
    else write('reading log: ',fname,' ');
    assign(fhandle,fname);
    reset(fhandle);
    while not(eof(fhandle)) do
    begin
      readln(fhandle,line);
      if not(leftstr(line,1)=';') and (wordcount(line,':')>1) then
      begin
        try
          i:=strtoint(trim(wordget(line,1,':')));
        except
          on E : EConvertError do i:=0;
        end;
        if (i>0) and (i<=ns) and (pos('IGNORE',line)=0) then
          s[i-1].log:=trim(rightstr(line,length(line)-posc(':',line)-1));
      end;
    end;
    close(fhandle);
    writeln('.');
  end;
end;

procedure readnotes(ps: pointer; ns: word; fname: ansistring; pdlist: pointer; dcount: word);
var
  s: ^tsector;
  dlist: ^word;
  fhandle: text;
  done: boolean;
  line: ansistring;
  i: word;
begin
  s:=ps;
  dlist:=pdlist;
  if fileexists(fname) then
  begin
    if length(fname)>33 then write('reading notes: ...',rightstr(fname,30),' ')
    else write('reading notes: ',fname,' ');
    assign(fhandle,fname);
    reset(fhandle);
    done:=false;
    while not(done) and not(eof(fhandle)) do
    begin
      readln(fhandle,line);
      if line='--- end of notes ---' then done:=true;
      if line='' then done:=true;
      if not(leftstr(line,1)=';') and (wordcount(line,':')>1) and not(done) then
      begin
        try
          i:=strtoint(trim(wordget(line,1,':')));
        except
          on E : EConvertError do i:=0;
        end;
        if (i>0) and (i<=ns) then
          s[i-1].notes:=trim(rightstr(line,length(line)-posc(':',line)));
        if leftstr(s[i-1].notes,20)='distance reference #' then s[i-1].notes:='';
      end;
    end;
    close(fhandle);
    writeln('.');
  end;

  for i:=2 to dcount do
    if dlist[i-1]>0 then
      if s[dlist[i-1]-1].notes='' then
        case i of
          2: s[dlist[i-1]-1].notes:='terra';
          3: s[dlist[i-1]-1].notes:='alpha centauri';
          4: s[dlist[i-1]-1].notes:='rylos';
          5: s[dlist[i-1]-1].notes:='stardock';
          otherwise s[dlist[i-1]-1].notes:='distance reference #'+inttostr(i-5);
        end;
end;

procedure notesreport(ps:pointer; ns, mw: word; fname:ansistring; stype:byte);
var
  s: ^tsector;
  numnotes, numlog, i, j, k, l, num: word;
  fhandle: text;
  list, list2: ^word;
begin
  s:=ps; list:=nil;

  numnotes:=0;
  numlog:=0;
  for i:=1 to ns do
  begin
    if not(s[i-1].notes='') then numnotes+=1;
    if not(s[i-1].log='') then numlog+=1;
  end;

  if (numnotes>0) or (numlog>0) then
  begin
    l:=floor(log10(ns))+1;
    getmem(list,numnotes*sizeof(word));
    getmem(list2,numlog*sizeof(word));
    j:=0;
    for i:=1 to ns do
      if not(s[i-1].log='') then
      begin
        list2[j]:=i;
        j+=1;
        if j>=numlog then break;
      end;
    j:=0;
    for i:=1 to ns do
      if not(s[i-1].notes='') then
      begin
        list[j]:=i;
        j+=1;
        if j>=numnotes then break;
      end;

    assign(fhandle,fname);
    rewrite(fhandle);
    if length(fname)>33 then write('writing notes report: ...',rightstr(fname,30),' ')
    else write('writing notes report: ',fname,' ');

    case stype of
      0: begin
           for i:=1 to numnotes do
             writeln(fhandle,stringofchar(' ',l-length(inttostr(list[i-1]))),list[i-1],' : ',s[list[i-1]-1].notes);
           writeln(fhandle,'--- end of notes ---');
           writeln(fhandle,'');
           writeln(fhandle,s_sum(0,s,mw,l,3));
           for i:=1 to numnotes do
             writeln(fhandle,s_sum(list[i-1],s,mw,l,3));
           writeln(fhandle,'');
           writeln(fhandle,'--- begin log ---');
           for i:=1 to numlog do
             writeln(fhandle,stringofchar(' ',l-length(inttostr(list2[i-1]))),list2[i-1],' : ',s[list2[i-1]-1].log);
         end;
      1: begin
           // sort list alphabetically
           for i:=1 to numnotes do
           begin
             k:=i;
             for j:=i to numnotes do
               if (s[list[k-1]-1].notes>s[list[j-1]-1].notes) then k:=j;
             if k>i then
             begin
               num:=list[i-1];
               list[i-1]:=list[k-1];
               list[k-1]:=num;
             end;
           end;
           for i:=1 to numnotes do
             writeln(fhandle,stringofchar(' ',l-length(inttostr(list[i-1]))),list[i-1],' : ',s[list[i-1]-1].notes);
           writeln(fhandle,'--- end of notes ---');
           writeln(fhandle,'');
           writeln(fhandle,s_sum(0,s,mw,l,3));
           for i:=1 to numnotes do
             writeln(fhandle,s_sum(list[i-1],s,mw,l,3));
           writeln(fhandle,'');
           writeln(fhandle,'--- begin log ---');
           for i:=1 to numlog do
             writeln(fhandle,stringofchar(' ',l-length(inttostr(list2[i-1]))),list2[i-1],' : ',s[list2[i-1]-1].log);
         end;
      2: begin
           // sort list alphabetically
           for i:=1 to numnotes do
           begin
             k:=i;
             for j:=i to numnotes do
               if (s[list[k-1]-1].notes>s[list[j-1]-1].notes) then k:=j;
             if k>i then
             begin
               num:=list[i-1];
               list[i-1]:=list[k-1];
               list[k-1]:=num;
             end;
           end;
           for i:=1 to numnotes do
             writeln(fhandle,stringofchar(' ',l-length(inttostr(list[i-1]))),list[i-1],' : ',s[list[i-1]-1].notes);
           writeln(fhandle,'--- end of notes ---');
           writeln(fhandle,'');
           // sort list by sector
           for i:=1 to numnotes do
           begin
             k:=i;
             for j:=i to numnotes do
               if list[k-1]>list[j-1] then k:=j;
             if k>i then
             begin
               num:=list[i-1];
               list[i-1]:=list[k-1];
               list[k-1]:=num;
             end;
           end;
           writeln(fhandle,s_sum(0,s,mw,l,3));
           for i:=1 to numnotes do
             writeln(fhandle,s_sum(list[i-1],s,mw,l,3));
           writeln(fhandle,'');
           writeln(fhandle,'--- begin log ---');
           for i:=1 to numlog do
             writeln(fhandle,stringofchar(' ',l-length(inttostr(list2[i-1]))),list2[i-1],' : ',s[list2[i-1]-1].log);
         end;
    end; //case

    close(fhandle);
    freemem(list);
    writeln('.');
  end;
end;

function portq(i: word; k: tproducts; ps: pointer; min,max: word) : boolean;
var
  s: ^tsector;
  quan: word;
begin
  s:=ps;
  if s[i-1].pt=nil then portq:=false
  else
    with s[i-1].pt^ do
    begin
      if percent[k]=100 then quan:=quantity[k]
      else quan:=(100*quantity[k]) div (percent[k]+1);
      if (quan>=min) and (quan<=max) then portq:=true
      else portq:=false;
    end;
end;

procedure bigportsreport(ps:pointer; ns, mw: word; fname:ansistring);
var
  s: ^tsector;
  i, j, l: word;
  k: tproducts;
  fhandle: text;
  mask: byte;
begin
  s:=ps;
  assign(fhandle,fname);
  rewrite(fhandle);
  if length(fname)>33 then write('writing bigports report: ...',rightstr(fname,30),' ')
  else write('writing bigports report: ',fname,' ');

  l:=floor(log10(ns))+1;

  for k:=ore to equ do
  begin
    case k of
      ore: mask:=1;
      org: mask:=2;
      equ: mask:=4;
    end;
    for j:=1 to 3 do
    begin
      case k of
        ore: write(fhandle,'FUEL ORE SELLERS');
        org: write(fhandle,'ORGANICS SELLERS');
        equ: write(fhandle,'EQUIPMENT SELLERS');
      end;
      case j of
        1: writeln(fhandle,':  3001 - 20000');
        2: writeln(fhandle,': 20001 - 40000');
        3: writeln(fhandle,': 40001 - 65535');
      end;
      writeln(fhandle,' ',s_sum(0,s,mw,l,3));
      for i:=1 to ns do
        if not(s[i-1].pt=nil) then
          with s[i-1].pt^ do
            if (ptype and mask)=0 then
              case j of
                1: if portq(i,k,s,3001,20000) then writeln(fhandle,' ',s_sum(i,s,mw,l,3));
                2: if portq(i,k,s,20001,40000) then writeln(fhandle,' ',s_sum(i,s,mw,l,3));
                3: if portq(i,k,s,40001,65535) then writeln(fhandle,' ',s_sum(i,s,mw,l,3));
              end;
    end;
    writeln(fhandle,'');
  end;

  for k:=ore to equ do
  begin
    case k of
      ore: mask:=1;
      org: mask:=2;
      equ: mask:=4;
    end;
    for j:=1 to 3 do
    begin
      case k of
        ore: write(fhandle,'FUEL ORE BUYERS');
        org: write(fhandle,'ORGANICS BUYERS');
        equ: write(fhandle,'EQUIPMENT BUYERS');
      end;
      case j of
        1: writeln(fhandle,':  3001 - 20000');
        2: writeln(fhandle,': 20001 - 40000');
        3: writeln(fhandle,': 40001 - 65535');
      end;
      writeln(fhandle,' ',s_sum(0,s,mw,l,3));
      for i:=1 to ns do
        if not(s[i-1].pt=nil) then
          with s[i-1].pt^ do
            if (ptype and mask)=mask then
              case j of
                1: if portq(i,k,s,3001,20000) then writeln(fhandle,' ',s_sum(i,s,mw,l,3));
                2: if portq(i,k,s,20001,40000) then writeln(fhandle,' ',s_sum(i,s,mw,l,3));
                3: if portq(i,k,s,40001,65535) then writeln(fhandle,' ',s_sum(i,s,mw,l,3));
              end;
    end;
    writeln(fhandle,'');
  end;

  close(fhandle);
  writeln('.');
end;

procedure bubblehunt(ps: pointer; ns, mw: word; fname: ansistring);
var
  s: ^tsector;
  i, j, maxd, mon: word;
  lns: byte;
  done, flag1: boolean;
  fhandle: text;
begin
  s:=ps;
  assign(fhandle,fname);
  rewrite(fhandle);
  writeln(fhandle,'bubble hunt report');
  if length(fname)>33 then write('writing bubble hunt report: ...',rightstr(fname,30),' ')
  else write('writing bubble hunt report: ',fname,' ');
  lns:=floor(log10(ns))+1;
  done:=false;
  j:=2;
  maxd:=j;
  mon:=spinner(0,500);
  while not(done) do
  begin
    flag1:=false;
    for i:=1 to ns do
    begin
      with s[i-1] do
        if not(bu=nil) then
        begin
          maxd:=max(ds_to[1],maxd);
          if ds_to[1]=j then
          begin
            maxd:=max(ds_to[1],maxd);
            if not(flag1) then
            begin
              writeln(fhandle,'bubbles (',j,') hop(s) from terra:');
              writeln(fhandle,' ',s_sum(0,s,mw,lns,1));
              flag1:=true;
            end;
            writeln(fhandle,' ',s_sum(i,s,mw,lns,1));
            mon:=spinner(mon,500);
          end;
        end;
    end;
    if j=maxd then done:=true
    else j+=1;
  end;
  close(fhandle);
  writeln('.');
end;
