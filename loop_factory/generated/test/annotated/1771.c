int main1(){
  int hu0, i5, po2, bqo1;
  hu0=72;
  i5=0;
  po2=i5;
  bqo1=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i5 <= hu0;
  loop invariant po2 == i5*(i5 + 1)*(2*i5 + 1)/6;
  loop invariant bqo1 >= 0;
  loop invariant i5 >= 0;
  loop assigns i5, po2, bqo1;
*/
while (1) {
      if (!(i5 < hu0)) {
          break;
      }
      i5 += 1;
      po2 = po2 + i5 * i5;
      bqo1 = bqo1*2+(po2%6)+3;
  }
}