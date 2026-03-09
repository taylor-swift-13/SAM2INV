int main1(int f,int h){
  int xu, dcdv, oj, q;
  xu=64;
  dcdv=0;
  oj=dcdv;
  q=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q == 5 + (oj*(oj+1))/2;
  loop invariant f == \at(f,Pre) + 2*oj;
  loop invariant h == \at(h,Pre) + (oj*(oj+1))/2;
  loop invariant 0 <= oj <= xu;
  loop assigns oj, q, f, h;
*/
while (1) {
      if (!(oj<xu)) {
          break;
      }
      oj++;
      q = q + oj;
      f += 2;
      h = h + oj;
  }
}