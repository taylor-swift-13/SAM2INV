int main1(int p,int h){
  int r1d, uje, j6;
  r1d=p+5;
  uje=1;
  j6=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j6 >= 0;
  loop invariant uje >= 1;
  loop invariant p == \at(p,Pre) + j6;
  loop invariant h == \at(h,Pre) + (j6*(j6+1))/2;
  loop invariant r1d == \at(p, Pre) + 5;
  loop assigns j6, uje, p, h;
*/
while (uje<=r1d) {
      j6++;
      uje = 2*uje;
      p++;
      h += j6;
  }
}