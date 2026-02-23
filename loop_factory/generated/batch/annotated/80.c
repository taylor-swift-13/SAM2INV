int main1(int b,int k){
  int a, t, x, v, l;

  a=k+4;
  t=0;
  x=b;
  v=b;
  l=-1;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant a == k + 4;

  loop invariant x == b + t;
  loop invariant v == b - t;
  loop invariant t >= 0;
  loop invariant x == \at(b, Pre) + t;
  loop invariant v == \at(b, Pre) - t;
  loop invariant a == \at(k, Pre) + 4;
  loop invariant 0 <= t;
  loop invariant a < 0 || t <= a;
  loop assigns x, v, t;
*/
while (t<a) {
      x = x+1;
      v = v-1;
      t = t+1;
  }

}
