int main1(){
  int j, xm, bf2l, e;
  j=(1%35)+9;
  xm=0;
  bf2l=j;
  e=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == 10 + 10*xm + (5*xm*(xm+1))/2;
  loop invariant 0 <= xm <= j;
  loop invariant bf2l == j + 5*xm;
  loop invariant j == (1%35) + 9;
  loop assigns bf2l, e, xm;
*/
while (1) {
      if (!(xm<=j-1)) {
          break;
      }
      bf2l = bf2l + 5;
      e += bf2l;
      xm++;
  }
}