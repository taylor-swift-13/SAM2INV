int main1(int n,int p){
  int h, i, l;

  h=(n%18)+10;
  i=0;
  l=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == (\at(n, Pre) % 18) + 10;
  loop invariant i == 0;
  loop invariant l == 1 || l == (\at(n, Pre));
  loop invariant p == \at(p, Pre);
  loop invariant i == 0 && h == (n % 18) + 10;
  loop invariant l == n || l == 1;
  loop invariant h == (\at(n,Pre) % 18) + 10;
  loop invariant n == \at(n,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant h == \at(n, Pre) % 18 + 10;
  loop invariant n == \at(n, Pre);
  loop invariant l == 1 || l == \at(n, Pre);
  loop invariant h == (\at(n,Pre) % 18) + 10 && (l == n || l == 1);
  loop invariant (l == n) || (l == 1);
  loop assigns l;
*/
while (1) {
      l = l+3;
      l = l-l;
      if ((i%4)==0) {
          l = l+1;
      }
  }

}
