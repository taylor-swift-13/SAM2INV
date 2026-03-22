int main1(int y){
  int q, nf, e5;
  q=0;
  nf=(y%20)+10;
  e5=(y%15)+8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nf == ((\at(y,Pre) % 20) + 10) - ((q + 1) / 2);
  loop invariant e5 == ((\at(y,Pre) % 15) + 8) - (q / 2);
  loop invariant q >= 0;
  loop assigns nf, e5, q;
*/
for (; nf>0&&e5>0; q += 1) {
      if (q%2==0) {
          nf = nf - 1;
      }
      else {
          e5 -= 1;
      }
  }
}