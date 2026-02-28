int main1(int a,int k){
  int l, u, g;

  l=50;
  u=l;
  g=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 50;
  loop invariant l == 50;
  loop invariant g >= a;
  loop invariant (g - a) % 2 == 0;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (g - \at(a, Pre)) % 2 == 0;
  loop invariant u >= 0;
  loop invariant u <= 50;
  loop invariant ((g - a) % 2 == 0);
  loop invariant ((g - a) % 2) == 0;
  loop assigns g;
*/
while (u>0) {
      g = g+2;
  }

}
