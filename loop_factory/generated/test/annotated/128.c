int main1(){
  int ag, h, sdfm, cx3;
  ag=1+6;
  h=0;
  sdfm=-8;
  cx3=ag;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= h;
  loop invariant h <= ag;
  loop invariant cx3 == ag*(1 + h) - (h*(h+1))/2;
  loop invariant (h == 0 ==> sdfm == -8) && (h > 0 ==> sdfm == ag - h);
  loop assigns h, sdfm, cx3;
*/
while (1) {
      if (!(h<ag)) {
          break;
      }
      h += 1;
      sdfm = (ag)+(-(h));
      cx3 += sdfm;
  }
}