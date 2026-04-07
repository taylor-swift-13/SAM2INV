int main1(){
  int o, u0w, nx, bw;
  o=1-5;
  u0w=o+3;
  nx=0;
  bw=o;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bw == o * (nx + 1);
  loop invariant (u0w == o) || (u0w == o + 3);
  loop invariant bw - o*nx == (1 - 5);
  loop invariant u0w >= o;
  loop invariant nx >= 0;
  loop invariant u0w <= o + 3;
  loop assigns bw, nx, u0w;
*/
while (u0w>o) {
      nx += 1;
      bw = bw + o;
      u0w = o;
  }
}