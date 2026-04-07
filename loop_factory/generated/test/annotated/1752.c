int main1(){
  int i2, ag, yfc, ic, rmw, cpuk;
  i2=1+4;
  ag=0;
  yfc=ag;
  ic=0;
  rmw=ag;
  cpuk=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rmw == -ag;
  loop invariant ic == - ((ag * (ag - 1)) / 2);
  loop invariant yfc == - ((ag * (ag + 1)) / 2);
  loop invariant 0 <= ag <= i2;
  loop invariant i2 == 5;
  loop assigns ag, ic, rmw, yfc;
*/
while (1) {
      if (!(ag < i2)) {
          break;
      }
      ag += 1;
      ic += rmw;
      rmw = rmw + cpuk;
      yfc += rmw;
  }
}