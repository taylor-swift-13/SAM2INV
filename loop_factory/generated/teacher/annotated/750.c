int main1(int a,int b,int k,int m){
  int t, g, e, c, u;

  t=k-2;
  g=t;
  e=t;
  c=g;
  u=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e*e - 4*c - t*t + 4*t == 0;
  loop invariant e >= t;
  loop invariant ((e - t) % 2 == 0);
  loop invariant g == t;
  loop invariant c >= t;
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant 4*(c - t) == e*e - t*t;
  loop invariant t == k - 2;
  loop invariant c - g == (e*e - t*t) / 4;
  loop invariant g == \at(k,Pre) - 2;
  loop invariant t == \at(k,Pre) - 2;
  loop invariant 4*c == e*e - g*g + 4*g;
  loop invariant e - g >= 0;
  loop invariant ((e - g) % 2) == 0;
  loop invariant e >= g;
  loop invariant c >= e;
  loop invariant c >= g;
  loop assigns e, c;
*/
while (g-2>=0) {
      e = e+1;
      c = c+e;
      e = e+1;
  }

}
