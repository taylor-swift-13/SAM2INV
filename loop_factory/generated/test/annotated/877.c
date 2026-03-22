int main1(){
  int a95, y, g9u, p;
  a95=1+21;
  y=0;
  g9u=y;
  p=a95;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g9u <= p*p;
  loop invariant a95 >= y;
  loop invariant y == 0;
  loop invariant p >= a95;
  loop assigns p, g9u, a95;
*/
while (y+1<=a95) {
      p++;
      g9u = p*p;
      a95 = (y+1)-1;
  }
}