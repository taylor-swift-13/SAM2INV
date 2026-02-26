int main1(int k,int n){
  int b, g, e, l;

  b=(n%8)+16;
  g=0;
  e=k;
  l=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= g;
  loop invariant g <= b;

  loop invariant e == k;
  loop invariant k == \at(k, Pre);
  loop invariant g >= 0;
  loop invariant b == (\at(n,Pre) % 8) + 16;
  loop invariant e == \at(k,Pre);
  loop invariant b == ((\at(n,Pre) % 8) + 16);
  loop invariant l * k >= 0;
  loop invariant (k == 0) ==> (l == 0);
  loop invariant b == (n % 8) + 16;
  loop invariant (l + e) % 2 == 0;
  loop invariant g == 0 ==> l == k;
  loop assigns g, l;
*/
while (g<=b-1) {
      l = l+l;
      l = l+e;
      g = g+1;
  }

}
