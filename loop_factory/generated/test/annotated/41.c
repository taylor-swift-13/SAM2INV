int main1(int y,int v){
  int umtq, h8, rtn, wk, l, mh;
  umtq=v+10;
  h8=umtq;
  rtn=1;
  wk=0;
  l=-2;
  mh=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wk == ((rtn - 1) * rtn * (2 * rtn - 1)) / 6;
  loop invariant l == rtn - 3;
  loop invariant v == \at(v, Pre) + (rtn - 1) * h8;
  loop invariant umtq == \at(v, Pre) + 10;
  loop invariant h8 == umtq;
  loop invariant mh == (rtn * rtn + rtn + 14) / 2;
  loop invariant 1 <= rtn;
  loop assigns wk, mh, rtn, v, l;
*/
while (1) {
      if (!(rtn<=umtq)) {
          break;
      }
      wk = wk+rtn*rtn;
      mh = mh + 3;
      rtn++;
      v += h8;
      l = l + 1;
      mh += l;
  }
}