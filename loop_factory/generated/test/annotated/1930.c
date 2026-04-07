int main1(){
  int dj, ws, c0lr, v5q;
  dj=(1%36)+11;
  ws=0;
  c0lr=1;
  v5q=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v5q == 1 + ws * dj;
  loop invariant 0 <= ws;
  loop invariant ws <= dj;
  loop invariant c0lr >= 1;
  loop invariant c0lr % 2 == 1;
  loop invariant dj == (1%36) + 11;
  loop assigns v5q, ws, c0lr;
*/
while (ws < dj) {
      v5q += dj;
      ws = ws + 1;
      c0lr = 2*c0lr+1;
  }
}