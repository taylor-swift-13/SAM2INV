int main1(){
  int ny, vvw, q, jo;
  ny=(1%25)+7;
  vvw=0;
  q=0;
  jo=ny;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((vvw == 0) ==> (jo == ny));
  loop invariant ((vvw == 0) ==> (q == 0));
  loop invariant ((vvw != 0) ==> (jo == 2 * ny));
  loop invariant vvw <= ny;
  loop invariant (ny - vvw) >= 0;
  loop invariant 0 <= vvw && vvw <= ny;
  loop invariant ny > 0;
  loop invariant (jo % ny) == 0;
  loop invariant (0 <= q) && (q <= 1);
  loop invariant (vvw <= ny);
  loop invariant (q == 0) || (q == 1);
  loop invariant jo == ny * (q + 1);
  loop invariant jo == ny * (1 + (vvw / ny)) && q == (vvw != 0) && 0 <= vvw <= ny;
  loop assigns jo, q, vvw;
*/
while (1) {
      if (!(vvw < ny)) {
          break;
      }
      jo = jo + ny;
      q = (vvw = vvw + 1) % 2;
      vvw = ny;
  }
}