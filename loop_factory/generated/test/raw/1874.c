int main1(){
  int jb2h, jp, kw, dr, d, r6, a, qly, s1g9;

  jb2h=(1%19)+16;
  jp=0;
  kw=jb2h;
  dr=-8;
  d=-8;
  r6=2;
  a=jb2h;
  qly=jp;
  s1g9=8;

  while (jp < jb2h) {
      jp += 1;
      if (!(!(jp % 2 == 0))) {
          kw++;
          qly = qly + 1;
      }
      else {
          kw -= 1;
          qly--;
      }
      if ((jp%6)==0) {
          s1g9 += dr;
      }
      dr++;
      a = a+qly-kw;
      a = dr+d+r6;
      dr++;
      if (dr+4<jb2h) {
          d++;
      }
      else {
          s1g9 += jp;
      }
  }

}
