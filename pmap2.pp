program pmap2;

// stacksize, heapsize \\
{$M 524288, 3145728}

uses sysutils, strings, math, dos, crt;

const
  fullversion=TRUE;
  vnum='0.38';
  vdate='april 2016';

{$include pmap2.inc}

var
  pstr1, pstr2: ansistring;
  pdelim, ch: char;
  i, k: integer;
  f: boolean;

  spath, gname, distanceanalysis, rpath, mname: ansistring;
  bubanalysis, secanalysis, createreports, screenpause: boolean;
  numsecs: integer;
  mergemode: byte;
  alpha, rylos, stardock: word;

procedure readmap(ps: pointer; ns: word; fname:ansistring; plhandle: pointer);
var
  s: ^tsector;
  lhandle: ^text;
  rec: ^byte;
  reclen: byte;
  fhandle: file of byte;

  w: array[0..5] of word;
  wtype: byte;
  p: tport;
  pe: boolean;
  numread, oldq, newq: word;
  i, j, j1, j2, m, n: word;
  k: tproducts;
  flag1: boolean;
  str1, str2: ansistring;

begin
  s:=ps;
  numread:=0;
  lhandle:=plhandle;
  rec:=nil;
  if fileexists(fname) then
  begin
    if fileexists(fname) then
    begin
      write(lhandle^,' ',fname,': ');
      if length(fname)>33 then write('reading map file: ...',rightstr(fname,30),' ')
      else write('reading map file: ',fname,' ');
      assign(fhandle, fname);
      reset(fhandle);
      read(fhandle,reclen);
      write('(reclen=',reclen,') ');
      writeln(lhandle^,'(reclen=',reclen,') ');
      writeln(lhandle^,'  comparing recent cim data with previous map data...');
      getmem(rec,reclen*sizeof(byte));
      for j:=0 to 5 do
        w[j]:=0;
      i:=0;
      while not(eof(fhandle)) and (sizeof(fhandle)>reclen) do
      begin
        if i>=ns then
        begin
          writeln(lhandle^,'  warning - map file contains too many sectors - proceed with caution.');
          break;
        end;
        blockread(fhandle,rec^,reclen,numread);
        if numread<reclen then break;
        i+=1;
        pe:=(rec[0] and 8)=8;

        if pe then
        begin
          p.v:=(rec[0] and 16)=16;
          p.ptype:=byte(rec[0] div 32);
          for k:=ore to equ do
          begin
            j:=word(k);
            p.quantity[k]:=rec[j*3+1]+rec[j*3+2]*256;
            p.percent[k]:=rec[j*3+3];
            if s[i-1].pt=nil then writeln(lhandle^,'  ',i,': new port found.')
            else
            begin
              oldq:=p.quantity[k];
              if p.percent[k]<100 then oldq:=(100*oldq) div (p.percent[k]+1);
              newq:=s[i-1].pt^.quantity[k];
              if s[i-1].pt^.percent[k]<100 then newq:=(100*newq) div (s[i-1].pt^.percent[k]+1);
              if (newq-oldq)>(oldq div 100) then
              begin
                write(lhandle^,'  ',i,': ');
                case k of
                  ore: write(lhandle^,'fuel ore up by ');
                  org: write(lhandle^,'organics up by ');
                  equ: write(lhandle^,'equipment up by ');
                end;
                writeln(lhandle^,newq-oldq,'.');
              end;
            end;
          end;
        end;

        n:=0;
        m:=(reclen-15) div 2;
        for j:=0 to m do
        begin
          w[n]:=rec[j*2+15]+rec[j*2+16]*256;
          wtype:=w[n] div 20000;
          w[n]:=w[n] mod 20000;
          if wtype>1 then w[n]:=0
          else n+=1;
          if n>5 then break;
        end;
        n:=0;
        for j:=0 to 5 do
          if w[j]>0 then n+=1;
        flag1:=false;
        if s[i-1].wp=nil then
        begin
          if n>0 then flag1:=true;
        end
        else
        begin
          if s[i-1].wp^.nw>n then flag1:=true
          else
          begin
            for j1:=1 to s[i-1].wp^.nw do
            begin
              flag1:=true;
              for j2:=1 to n do
                if s[i-1].wp^.warps[j1-1]=w[j2-1] then flag1:=false;
              if flag1 then break;
            end;
          end;
        end;
        if flag1 then
        begin
          write(lhandle^,'  ',i,': new warps found (');
          if (n<6) and not(s[i-1].wp=nil) then
          begin
            j1:=1;
            j2:=1;
            m:=0;
            str1:='';
            str2:='';
            while (j1<=n) and (j2<=s[i-1].wp^.nw) do
            begin
              if w[j1-1]=s[i-1].wp^.warps[j2-1] then
              begin
                if str1='' then str1:=inttostr(w[j1-1])
                else str1:=str1+';'+inttostr(w[j1-1]);
                j1+=1;
                j2+=1;
              end
              else
              begin
                if w[j1-1]<s[i-1].wp^.warps[j2-1] then
                begin
                  if str1='' then str1:=inttostr(w[j1-1])
                  else str1:=str1+';'+inttostr(w[j1-1]);
                  j1+=1;
                end
                else
                begin
                  if w[j1-1]>s[i-1].wp^.warps[j2-1] then
                  begin
                    if str1='' then str1:=inttostr(s[i-1].wp^.warps[j2-1])
                    else str1:=str1+';'+inttostr(s[i-1].wp^.warps[j2-1]);
                    if str2='' then str2:=inttostr(s[i-1].wp^.warps[j2-1])
                    else str2:=str2+' '+inttostr(s[i-1].wp^.warps[j2-1]);
                    j2+=1;
                  end;
                end;
              end;
              m+=1;
            end;
            if j1<=n then
            begin
              m+=n-j1+1;
              for j:=j1 to n do
              begin
                if str1='' then str1:=inttostr(w[j-1])
                else str1:=str1+';'+inttostr(w[j-1]);
              end;
            end;
            if j2<=s[i-1].wp^.nw then
            begin
              m+=s[i-1].wp^.nw-j2+1;
              for j:=j2 to s[i-1].wp^.nw do
              begin
                if str1='' then str1:=inttostr(s[i-1].wp^.warps[j-1])
                else str1:=str1+';'+inttostr(s[i-1].wp^.warps[j-1]);
                if str2='' then str2:=inttostr(s[i-1].wp^.warps[j-1])
                else str2:=str2+' '+inttostr(s[i-1].wp^.warps[j-1]);
              end;
            end;
            n:=m;
          end;
          writeln(lhandle^,str2,')');// ,str1,' n=',n);
{
          getmem(wtemp,sizeof(twarps));
          getmem(wtemp^.warps,n*sizeof(word));
          getmem(wtemp^.warptype,n*sizeof(byte));
}
        end;

      end;

      if i<ns then writeln(lhandle^,'  warning - map file contains too few sectors - proceed with caution.');
      freemem(rec);
      close(fhandle);
      writeln('.');
      writeln(lhandle^,'  ',i,' sectors read.');
    end;
  end;
end;

procedure main(fname, spath, rpath: ansistring;
               ns: word;
               mm: byte;
               dstr: ansistring;
               fsa, fbu, fcr: boolean;
               mname: ansistring);
var
  s: ^tsector;
  dlist: ^word;
  dcount: word;

  i, j, mw: word;
  lhandle: text;

begin
  s:=nil; dlist:=nil;

  // reserve memory for the dlists and set values \\
  dcount:=5;
  for i:=6 to wordcount(dstr,';') do
    try
      j:=strtoint(wordget(dstr,i,';'));
      if (j>0) and (j<=ns) then dcount+=1;
    except
    end;

  if dcount>0 then
  begin
    getmem(dlist,dcount*sizeof(word));
    i:=1;
    while i<=dcount do
      try
        dlist[i-1]:=strtoint(wordget(dstr,i,';'));
        if (i<=5) or ((dlist[i-1]>0) and (dlist[i-1]<=ns)) then i+=1;
      except
        on E : EConvertError do dlist[i-1]:=0;
      end;
  end;

  // reserve memory for the sectors and initialize variables where necessary \\
  getmem(s, ns*sizeof(tsector));
  for i:=1 to ns do
  begin
    with s[i-1] do
    begin
      v:=false;
      figs:=false;
      wp:=nil;
      pt:=nil;
      bu:=nil;
      sid:=nil;
      notes:='';
      log:='';
      if dcount>0 then
      begin
        getmem(ds_to,dcount*sizeof(byte));
        getmem(ds_from,dcount*sizeof(byte));
        for j:=1 to dcount do
        begin
          ds_to[j-1]:=255;
          ds_from[j-1]:=255;
        end;
      end
      else
      begin
        ds_to:=nil;
        ds_from:=nil;
      end;
    end;
  end;

  // backwards compatibility \\
  if not(fileexists(spath+fname+'_ref.sct') or fileexists(spath+fname+'_ref.prt')) then
  begin
    if fileexists(spath+fname+'.map') then deletefile(spath+fname+'.map');
    if fileexists(spath+fname+'.fig') then deletefile(spath+fname+'.fig');
    if fileexists(spath+fname+'.vod') then deletefile(spath+fname+'.vod');
  end;
  if fileexists(spath+fname+'.srf') and not(fileexists(spath+fname+'_ref.sct')) then
    renamefile(spath+fname+'.srf',spath+fname+'_ref.sct');
  if fileexists(spath+fname+'.prf') and not(fileexists(spath+fname+'_ref.prt')) then
    renamefile(spath+fname+'.prf',spath+fname+'_ref.prt');

  // set up log file \\
  {$i-}
  assign(lhandle,rpath+fname+'_changelog.txt');
  append(lhandle);
  {$i+}
  if ioresult > 0 then rewrite(lhandle);
  writeln(lhandle,'[',formatdatetime('yy-mm-dd hh:mm:ss',now),'] BEGIN PMAP2 RECORD:');

  // read fig data \\
  readfigs(s,ns,spath+fname+'_figs.txt',@lhandle);

  // read sector data \\
  if (mm and 1)=1 then
  begin
    readsectorcim(s, ns, spath+fname+'.sct', 0, true, @lhandle);
    readportcim(s, ns, spath+fname+'.prt', 0, true, @lhandle);
  end;
  if ((mm and 2)=2) and ((mm and 4)=4) then
  begin
    readsectorcim(s, ns, spath+fname+'_ref.sct', 1, false, @lhandle);
    readportcim(s, ns, spath+fname+'_ref.prt', 1, false, @lhandle);
    readmap(s, ns, spath+fname+'.map', @lhandle);
  end
  else
  begin
    if (mm and 2)=2 then
    begin
      readsectorcim(s, ns, spath+fname+'_ref.sct', 1, false, @lhandle);
      readportcim(s, ns, spath+fname+'_ref.prt', 1, false, @lhandle);
    end;
    if (mm and 4)=4 then readmap(s, ns, spath+fname+'.map', @lhandle);
  end;

  if (not(mname='') and fileexists(mname)) then
  begin
    if (extractfileext(mname)='.sct') then
      readsectorcim(s, ns, mname, 2, false, @lhandle);
    if (extractfileext(mname)='.prt') then
      readportcim(s, ns, mname, 2, false, @lhandle);
    if (extractfileext(mname)='.ztm') then
      readztm(s, ns, mname, @lhandle);
  end;

  readlog(s, ns, spath+fname+'_log.txt');
  readnotes(s, ns, rpath+fname+'_notes.txt',dlist,dcount);
  reconcile(s, ns, @mw, @lhandle);

  if fileexists(spath+fname+'_bak.sct') then
    deletefile(spath+fname+'_bak.sct');
  if fileexists(spath+fname+'_ref.sct') then
    renamefile(spath+fname+'_ref.sct',spath+fname+'_bak.sct');
  writesectorcim(s,ns,spath+fname+'_ref.sct',@lhandle);

  if fileexists(spath+fname+'_bak.prt') then
    deletefile(spath+fname+'_bak.prt');
  if fileexists(spath+fname+'_ref.prt') then
    renamefile(spath+fname+'_ref.prt',spath+fname+'_bak.prt');
  writeportcim(s,ns,spath+fname+'_ref.prt',@lhandle);

  if fcr then
  begin
    distcalc(s,ns,dlist,dcount);
    mslcalc(s,ns,dlist,dcount,rpath+fname+'_msl.txt');
    if fbu then bubbleanalysis(s,ns,mw,rpath+fname+'_bubbles.txt');
    writemap(s,ns,spath+fname+'.map');
    oneways(s,ns,rpath+fname+'_oneways.txt');
    if fullversion then blockedports(s,ns,rpath+fname+'_blockedports.txt');
    portpairreport(s,ns,rpath+fname+'_portpairs.txt');
    if fullversion then bigportsreport(s,ns,mw,rpath+fname+'_bigports.txt');
    distancereport(s,ns,dlist,dcount,rpath+fname+'_distance.txt');
    specialportreport(s,ns,mw,rpath+fname+'_special.txt');
    if fullversion then deadends(s,ns,mw,rpath+fname+'_deadends.txt');
    if fullversion then bubblehunt(s,ns,mw,rpath+fname+'_bubblehunt.txt');
    if fullversion then onewaytunnels(s,ns,rpath+fname+'_oneway-tunnels.txt');
    notesreport(s,ns,mw,rpath+fname+'_notes.txt',2);
    dumpreport(s,ns,mw,rpath+fname+'_dump.txt');
    if fsa and fbu and fullversion then secludedanalysis(s,ns,mw,rpath+fname+'_secludeds.txt');
  end;

  // close log file \\
  writeln(lhandle,'[END OF RECORD]');
  writeln(lhandle,'');
  close(lhandle);

  // to write:
    // readmap
    // writemap

  // free memory here \\
  for i:=1 to ns do
  begin
    with s[i-1] do
    begin
      if not(wp=nil) then
      begin
        if not(wp^.warptype=nil) then freemem(wp^.warptype);
        if not(wp^.warps=nil) then freemem(wp^.warps);
        freemem(wp);
      end;
      if not(pt=nil) then freemem(pt);
      if not(bu=nil) then freemem(bu);
      if not(sid=nil) then freemem(sid);
      if not(ds_to=nil) then freemem(ds_to);
      if not(ds_from=nil) then freemem(ds_from);
      if not(notes='') then notes:='';
    end;
  end;
  if not(s=nil) then begin freemem(s); s:=nil; end;
  if not(dlist=nil) then begin freemem(dlist); dlist:=nil; end;
end;

procedure usage(error:ansistring; code:word);
var
  ch: char;
begin
  writeln;
  if not(error='') and not(error='halt') then writeln('error:  ',error);
  if fullversion then writeln('usage:  pmap2 /g:gamename * - cim filename without the extension')
                 else writeln('usage: pmap2a /g:gamename * - cim filename without the extension');
                      writeln('              /n:#          - number of sectors, [1..20000]');
                      writeln('              /b-           - do not perform bubble analysis');
  if fullversion then writeln('              /s+           - perform secluded analysis **');
//                    writeln('              /mm:#         - mergemode, 1=cim, 2=ref, 3=cim+ref');
//                    writeln('                               4=map, 5=cim+map, 6=ref+map, 7=cim+ref+map');
                      writeln('              /al:#         - sector location of alpha centauri');
                      writeln('              /ry:#         - sector location of rylos');
                      writeln('              /sd:#         - sector location of stardock');
                      writeln('              /d:#;#;#      - sectors to include in distance analysis');
                      writeln('              /p:path       - destination path for report files');
                      writeln('                          * - required parameter');
  if fullversion then writeln('                         ** - if /b- then /s+ is ignored');
  if fullversion then writeln('defaults: /n:20000 /mm:7 /b+ /s-')
                 else writeln('defaults: /n:20000 /mm:7 /b+');
  if not(error='') or (error='halt') then
  begin
    if screenpause then
    begin
      writeln('press a key to continue...');
      ch:=readkey;
    end;
    halt(code);
  end;
end;

// MAIN BODY \\
begin

  cursoroff;
  clrscr;
  if fullversion then writeln('PMAP2 v.',vnum,' ',vdate,' by the reverend')
  else writeln('PMAP2a v.',vnum,' ',vdate,' by the reverend');

  // define default variables \\
  gname:='';
  numsecs:=20000;
  bubanalysis:=true;
  secanalysis:=false;
  createreports:=true;
  screenpause:=false;
  distanceanalysis:='';
  mergemode:=3;
  rylos:=0;
  alpha:=0;
  stardock:=0;
  rpath:='';
  spath:='';
  mname:='';

  // read through parameters \\
  for i:=1 to paramcount do
  begin
    k:=paramcheck(paramstr(i));
    if k=0 then usage('invalid parameter <'+paramstr(i)+'>.',1)
    else
    begin

      // split parameter parts \\
      pstr1:=leftstr(paramstr(i),k-1);
      if k>length(paramstr(i)) then pdelim:=' '
      else pdelim:=copy(paramstr(i),k,1)[1];
      if pdelim=':' then pstr2:=copy(paramstr(i),k+1,length(paramstr(i))-k)
      else pstr2:='';

      f:=false;
      try
        // define flags and variables \\
        if (pstr1='/?') then usage('halt',0);
        if (pstr1='/s') then begin f:=true;
                                   case pdelim of
                                     '-': ;
                                     '+': secanalysis:=true;
                                     else f:=false;
                             end;  end;
        if (pstr1='/b') then begin f:=true;
                                   case pdelim of
                                     '-': bubanalysis:=false;
                                     '+': ;
                                     else f:=false;
                             end;  end;
        if (pstr1='/r') then begin f:=true;
                                    case pdelim of
                                      '-': createreports:=false;
                                      '+': ;
                                      else f:=false;
                              end;  end;
        if (pstr1='/pause') then begin f:=true;
                                       case pdelim of
                                         '-': ;
                                         '+': screenpause:=true;
                                         else f:=false;
                                 end;  end;
        if (pstr1='/n')  and (pdelim=':') then begin f:=true; numsecs:=strtoint(pstr2);   end;
        if (pstr1='/d')  and (pdelim=':') then begin f:=true; distanceanalysis:=pstr2;    end;
        if (pstr1='/mm') and (pdelim=':') then begin f:=true; mergemode:=strtoint(pstr2); end;
        if (pstr1='/ry') and (pdelim=':') then begin f:=true; rylos:=strtoint(pstr2);     end;
        if (pstr1='/al') and (pdelim=':') then begin f:=true; alpha:=strtoint(pstr2);     end;
        if (pstr1='/sd') and (pdelim=':') then begin f:=true; stardock:=strtoint(pstr2);  end;
        if (pstr1='/g')  and (pdelim=':') then begin
                                                 pstr2:=setdirseparators(pstr2);
                                                 gname:=extractfilename(pstr2);
                                                 spath:=extractfilepath(pstr2);
                                                 f:=validfolder(spath);
                                               end;
        if (pstr1='/p')  and (pdelim=':') then begin
                                                 pstr2:=setdirseparators(pstr2);
                                                 if (length(pstr2)>0) and not(rightstr(pstr2,1)='\') then
                                                   pstr2:=setdirseparators(pstr2+'\');
                                                 rpath:=pstr2;
                                                 f:=validfolder(rpath);
                                               end;
        if (pstr1='/m')  and (pdelim=':') then begin
                                                 mname:=setdirseparators(pstr2);
                                                 f:=validfolder(extractfilepath(mname));
                                                 if not(f) then mname:='';
                                               end;
      except
        on E : EConvertError do
          usage('invalid parameter <'+paramstr(i)+'>.',1);
      end;

      if not(f) then usage('invalid parameter <'+paramstr(i)+'>.',1);

    end;
  end;

  if gname='' then usage('halt',1);

  if distanceanalysis='' then
    distanceanalysis:='0;1;'+inttostr(alpha)+';'+inttostr(rylos)+';'+inttostr(stardock)
  else
    distanceanalysis:='0;1;'+inttostr(alpha)+';'+inttostr(rylos)+';'+inttostr(stardock)+';'+distanceanalysis;

  // run mainprogram \\

//  try
    main(gname,spath,rpath,numsecs,mergemode,distanceanalysis,secanalysis,bubanalysis,createreports,mname);
//  except
//    writeln;
//    writeln('ERROR.  please email me at the.reverend@coastgames.com.');
//  end;


  cursoron;
  if screenpause then
  begin
    writeln('press a key to continue...');
    ch:=readkey;
  end;

end.
