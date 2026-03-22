int main1(){
  int ag, na, h5gr, v, de, o4, jo3, lv, p, jas;
  ag=1+22;
  na=ag;
  h5gr=0;
  v=0;
  de=0;
  o4=0;
  jo3=0;
  lv=0;
  p=0;
  jas=na;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h5gr >= 0;
  loop invariant h5gr <= ag;
  loop invariant v + de + o4 + jo3 == h5gr;
  loop invariant 0 <= h5gr <= ag &&
                   v == (h5gr + 9) / 10 &&
                   ((h5gr%3)==0 ==> p == 3*(h5gr/3)) &&
                   ((h5gr%3)==1 ==> p == 3*(h5gr/3) + 1) &&
                   ((h5gr%3)==2 ==> p == 3*(h5gr/3) + 3);
  loop assigns h5gr, p, lv, jas, v, de, o4, jo3;
*/
while (1) {
      if (!(h5gr<=ag-1)) {
          break;
      }
      if (h5gr%10==0) {
          v++;
      }
      else {
          if (h5gr%7==0) {
              de = de + 1;
          }
          else {
              if (h5gr%3==0) {
                  o4++;
              }
              else {
                  if (1) {
                      jo3++;
                  }
              }
          }
      }
      h5gr += 1;
      p = p+h5gr%3;
      lv = (lv+o4)%5;
      jas = (jas+h5gr)%3;
  }
}