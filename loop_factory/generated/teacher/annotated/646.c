int main1(int a,int q){
  int c, j, t, e, v, g;

  c=a;
  j=1;
  t=q;
  e=c;
  v=4;
  g=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant c == a;
  loop invariant e == a + 3*(g - a) + (g - a)*(g - a);
  loop invariant v == 4 + 2*(g - a);
  loop invariant t == q + (g - a) * a + ((g - a) * (g - a - 1) * (g - a + 4)) / 3;
  loop invariant e == a + (g - a)*(g - a) + 3*(g - a);
  loop invariant g - a <= 1;
  loop invariant g >= a;
  loop invariant g <= c + 1;
  loop invariant t == q + a*(g - a) + ((g - a)*(g - a - 1)*(g - a + 4))/3;
  loop assigns t, e, v, g;
*/
while (g<=c) {
      t = t+e;
      e = e+v;
      v = v+2;
      g = g+1;
  }

}
