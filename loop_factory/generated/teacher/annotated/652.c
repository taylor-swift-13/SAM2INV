int main1(int a,int b){
  int t, v, r, q, u, i;

  t=a+18;
  v=0;
  r=a;
  q=v;
  u=b;
  i=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant v >= 0;
  loop invariant ((r - a - v) % 2) == 0;
  loop invariant t == a + 18;
  loop invariant b == \at(b, Pre);

  loop assigns r, v;
*/
while (1) {
      r = r*3+5;
      v = v+1;
  }

}
