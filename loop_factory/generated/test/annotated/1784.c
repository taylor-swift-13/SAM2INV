int main1(int h){
  int zj, nr, r7, v5a;
  zj=(h%60)+60;
  nr=(h%9)+2;
  r7=0;
  v5a=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zj == (\at(h, Pre) % 60) + 60;
  loop invariant nr == (\at(h, Pre) % 9) + 2;
  loop invariant 0 <= r7;
  loop invariant h >= \at(h,Pre);
  loop invariant (v5a == 0) || (v5a == nr);
  loop assigns h, v5a, r7;
*/
while (zj>nr*r7+v5a) {
      if (!(!(v5a==nr-1))) {
          v5a++;
      }
      else {
          v5a = 0;
          r7++;
      }
      h += v5a;
  }
}