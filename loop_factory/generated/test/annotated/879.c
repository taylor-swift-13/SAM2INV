int main1(int v){
  int wr, cj, c9, qu;
  wr=v;
  cj=1;
  c9=cj;
  qu=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (cj == 1);
  loop invariant (wr == v || wr == 2);
  loop invariant qu >= 4;
  loop invariant ((qu == 4 && c9 == 1) || (c9 == qu*qu));
  loop assigns wr, qu, c9;
*/
while (cj*3<=wr) {
      qu += 1;
      c9 = qu*qu;
      wr = (cj*3)-1;
  }
}