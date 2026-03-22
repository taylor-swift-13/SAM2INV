int main1(){
  int f601, jrw, tjo, cg, bo;
  f601=(1%28)+8;
  jrw=(1%22)+5;
  tjo=0;
  cg=3;
  bo=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant cg >= 3;
  loop invariant tjo >= 0;
  loop invariant 0 <= jrw <= 6;
  loop invariant ((f601 == 9) || (f601 % 2 == 0));
  loop invariant f601 >= 9;
  loop invariant bo >= 8;
  loop assigns bo, cg, f601, jrw, tjo;
*/
while (jrw!=0) {
      if (jrw%2==1) {
          tjo = tjo + f601;
          jrw--;
      }
      f601 = 2*f601;
      jrw = jrw/2;
      bo = bo*3+(f601%2)+3;
      cg = cg + bo;
  }
}