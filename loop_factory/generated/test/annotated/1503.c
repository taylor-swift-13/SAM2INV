int main1(int i,int e){
  int g9, yx8q, s2, pt, vu, j, nmnp;
  g9=(e%30)+9;
  yx8q=g9+4;
  s2=0;
  pt=25;
  vu=20;
  j=yx8q;
  nmnp=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (yx8q == g9 + 4) || (yx8q == g9);
  loop invariant nmnp >= 6;
  loop invariant g9 == ((\at(e, Pre) % 30) + 9);
  loop invariant s2 >= 0;
  loop invariant pt >= 25;
  loop invariant i >= \at(i, Pre);
  loop assigns e, i, j, nmnp, pt, s2, vu, yx8q;
*/
while (1) {
      if (!(yx8q>g9)) {
          break;
      }
      if (vu==g9+1) {
          s2 = s2 + 3;
          pt = pt + 3;
      }
      else {
          s2 += 2;
          pt += 2;
      }
      if (!(!(vu==g9))) {
          s2 = s2 + 1;
          vu++;
      }
      i = i+(s2%2);
      j = j*3+4;
      nmnp = nmnp + s2;
      e = e+pt-vu;
      yx8q = g9;
  }
}