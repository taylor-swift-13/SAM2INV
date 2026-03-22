int main1(){
  int ljm2, rjsu, gt;
  ljm2=(1%31)+16;
  rjsu=-1;
  gt=rjsu;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ljm2 - rjsu) >= 0;
  loop invariant ljm2 == 17;
  loop invariant gt <= 0;
  loop invariant (gt == -1) || (gt % 3 == 0);
  loop invariant -1 <= rjsu;
  loop assigns gt, rjsu;
*/
while (1) {
      if (!(rjsu<=ljm2-1)) {
          break;
      }
      gt = gt*3;
      rjsu += 1;
  }
}