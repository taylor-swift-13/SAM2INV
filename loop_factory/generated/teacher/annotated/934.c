int main1(int m,int n){
  int g, i, c;

  g=(n%17)+17;
  i=0;
  c=g;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == (\at(n, Pre) % 17) + 17;
  loop invariant c >= (\at(n, Pre) % 17) + 17;
  loop invariant i >= 0;
  loop invariant c >= g;
  loop invariant c >= g * i;

  loop invariant (i > 0) ==> (c >= 2*g);
  loop invariant g == (n % 17) + 17;

  loop invariant g > 0;
  loop invariant g == ((\at(n, Pre) % 17) + 17);
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant g == (\at(n,Pre) % 17) + 17 && i >= 0;
  loop invariant c >= g && m == \at(m,Pre) && n == \at(n,Pre);
  loop invariant g == (\at(n,Pre) % 17) + 17;
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant g == \at(n,Pre) % 17 + 17 && m == \at(m,Pre) && n == \at(n,Pre);

  loop assigns c, i;
*/
while (1) {
      c = c+c;
      if (c+2<g) {
          c = c+1;
      }
      i = i+1;
  }

}
