int main1(int y,int v){
  int s, fn, rh;
  s=53;
  fn=s;
  rh=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y == \at(y, Pre);
  loop invariant v == \at(v, Pre);
  loop invariant s == 53;
  loop invariant fn <= s;
  loop invariant rh >= 0;
  loop invariant rh <= s;
  loop invariant (rh > 0) ==> (fn < s);
  loop assigns rh, fn;
*/
while (rh>0&&fn<s) {
      if (rh<rh) {
          rh = rh;
      }
      else {
          rh = rh;
      }
      rh -= rh;
      rh += rh;
      fn += 1;
  }
}