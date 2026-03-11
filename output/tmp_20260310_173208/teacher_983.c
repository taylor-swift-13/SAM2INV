int main1(int k,int p){
  int h, t, g;

  h=(k%7)+4;
  t=0;
  g=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant h == (\at(k, Pre) % 7) + 4;

  loop invariant g == \at(k, Pre) + (t*(t+1))/2;

  loop invariant h == \at(k, Pre) % 7 + 4 && k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant g == \at(k, Pre) + t*(t+1)/2;
  loop invariant 0 <= t;

  loop invariant h == (\at(k, Pre) % 7) + 4 && k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant g == \at(k, Pre) + t + (t*(t-1))/2;
  loop invariant k == \at(k, Pre) && p == \at(p, Pre);
  loop invariant h == ((\at(k,Pre) % 7) + 4);
  loop invariant h < 0 || t <= h;
  loop invariant g == \at(k,Pre) + t + t*(t-1)/2;
  loop invariant h == \at(k, Pre) % 7 + 4;
  loop assigns g, t;
*/
while (t<=h-1) {
      g = g+1;
      g = g+t;
      t = t+1;
  }
/*@
  assert !(t<=h-1) &&
         (k == \at(k, Pre));
*/


}
