int main1(){
  int szn, k3y, th, ygt1;
  szn=2;
  k3y=0;
  th=(1%28)+10;
  ygt1=szn;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant szn == 2;
  loop invariant (k3y >= 0);
  loop invariant (th >= 0);
  loop invariant (ygt1 >= 0);
  loop invariant th == ((1%28) + 10) - k3y*(k3y - 1)/2;
  loop assigns k3y, th, ygt1;
*/
while (th>k3y) {
      th = th - k3y;
      ygt1 += th;
      k3y = (1)+(k3y);
  }
}