int main1(int s,int y){
  int zt7, d5o, fi, lk;
  zt7=(s%15)+8;
  d5o=0;
  fi=-6;
  lk=y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (d5o == 0) ==> (y == \at(y, Pre));
  loop invariant (d5o > 0) ==> (y == fi + lk + s);
  loop invariant d5o >= 0;
  loop invariant zt7 == (s % 15) + 8;
  loop assigns y, d5o;
*/
while (1) {
      if (!(d5o<zt7)) {
          break;
      }
      y = fi+lk+s;
      d5o = d5o + 1;
  }
}