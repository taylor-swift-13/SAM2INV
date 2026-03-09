int main1(){
  int q, c, j, qx;
  q=1-10;
  c=0;
  j=0;
  qx=q;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == j % 4;
  loop invariant j >= 0;
  loop invariant qx == q + j*(q + 2);
  loop assigns c, j, qx;
*/
while (j<q) {
      c = (c+1)%4;
      j++;
      qx = qx + q;
      qx += 2;
  }
}