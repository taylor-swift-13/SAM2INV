int main1(int a,int b,int m,int q){
  int l, p, v, i, g, c, w, y;

  l=(a%29)+13;
  p=0;
  v=6;
  i=m;
  g=a;
  c=-3;
  w=l;
  y=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant l == \at(a, Pre) % 29 + 13;
  loop invariant i <= m;
  loop invariant b == \at(b,Pre);
  loop invariant q == \at(q,Pre);
  loop invariant i <= \at(m,Pre);
  loop invariant v >= 6;
  loop invariant g == \at(a,Pre);
  loop invariant i == \at(m,Pre) || i == \at(a,Pre);
  loop invariant (c == v + i + g) || (c == -3 && v == 6 && i == \at(m,Pre) && g == \at(a,Pre));
  loop invariant (i == m) || (i == a);
  loop invariant (c == v + i + g) || (v == 6 && i == m && c == -3);
  loop invariant i == \at(m,Pre) || i == g;
  loop invariant g == a;
  loop invariant l == (\at(a,Pre) % 29) + 13;
  loop assigns i, v, c;
*/
while (1) {
      if (g<=i) {
          i = g;
      }
      v = v+1;
      c = v+i+g;
  }

}
