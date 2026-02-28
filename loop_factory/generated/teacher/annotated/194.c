int main1(int a,int k){
  int l, u, g;

  l=50;
  u=l;
  g=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(a, Pre) + (50 - u) * (51 + u) / 2;
  loop invariant l == 50;
  loop invariant 0 <= u <= l;
  loop invariant g == a + (l - u) * (l + u + 1) / 2;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant g == (\at(a, Pre) + (50*51)/2 - u*(u+1)/2);
  loop invariant 0 <= u;
  loop invariant u <= 50;
  loop invariant g == a + 1275 - u*(u+1)/2;
  loop invariant (l == 50);
  loop invariant (0 <= u);
  loop invariant (u <= 50);
  loop invariant (k == \at(k, Pre));
  loop invariant g == \at(a, Pre) + 1275 - (u*(u+1))/2;
  loop invariant u >= 0;
  loop assigns g, u;
*/
while (u>0) {
      g = g+u;
      u = u-1;
  }

}
