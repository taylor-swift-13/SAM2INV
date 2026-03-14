int main1(){
  int q7, yz, s, xxd;
  q7=80;
  yz=0;
  s=0;
  xxd=10;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (s <= q7/2) ==> (xxd == 3*s + 10);
  loop invariant (0 <= s);
  loop invariant (s <= q7);
  loop invariant (yz == 0);
  loop invariant ((xxd - 10) % 6 == 0);
  loop invariant (xxd >= 10);
  loop invariant (xxd <= 10 + 6 * q7);
  loop invariant (s >= q7/2) ==> ((xxd - 10) == (yz + 6) * ((q7/2)/2 + (s - q7/2)));
  loop assigns s, xxd;
*/
while (1) {
      if (!(s<=q7-1)) {
          break;
      }
      if (s<q7/2) {
          s += 2;
      }
      else {
          s++;
      }
      xxd = xxd + yz;
      xxd += 6;
  }
}