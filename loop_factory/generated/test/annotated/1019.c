int main1(int u,int w){
  int tyk, g9b, b;
  tyk=u;
  g9b=-2;
  b=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tyk == \at(u, Pre);
  loop invariant g9b == -2 + (\at(u,Pre) - u);
  loop invariant u + b == 2 * \at(u,Pre);
  loop invariant w == \at(w,Pre) + (g9b + 2) * \at(u,Pre) + ((g9b + 2) * (g9b + 3)) / 2;
  loop invariant u <= tyk;
  loop assigns u, g9b, b, w;
*/
while (1) {
      if (!(g9b<=tyk-1)) {
          break;
      }
      u--;
      b += 1;
      w += b;
      g9b = g9b + 1;
  }
}