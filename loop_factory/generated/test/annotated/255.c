int main1(){
  int mu2, hx, y6b, u;
  mu2=62;
  hx=mu2;
  y6b=4;
  u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mu2 == 62;
  loop invariant u == 0;
  loop invariant (hx - mu2) >= 0;
  loop invariant (y6b - 4) == u * (hx - mu2);
  loop assigns hx, y6b;
*/
while (1) {
      if (!(hx-3>=0)) {
          break;
      }
      if (!(!(hx<mu2/2))) {
          y6b = y6b + 1;
      }
      else {
          y6b = y6b + u;
      }
      hx += 1;
  }
}