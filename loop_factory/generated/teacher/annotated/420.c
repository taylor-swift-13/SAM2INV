int main1(int a,int k){
  int u, i, g, h;

  u=27;
  i=u;
  g=-3;
  h=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == 27;
  loop invariant u == 27;
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (g + 3) % (1 + h) == 0;
  loop invariant g <= u + h;
  loop invariant g >= -3;

  loop invariant (g + 3) % (h + 1) == 0;
  loop assigns g;
*/
while (g<u) {
      if (g<u) {
          g = g+1;
      }
      g = g+h;
  }

}
