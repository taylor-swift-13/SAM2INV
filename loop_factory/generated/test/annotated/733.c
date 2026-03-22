int main1(int a){
  int cs, yq, kmzf;
  cs=0;
  yq=(a%28)+10;
  kmzf=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yq == (((\at(a, Pre) % 28) + 10) - ((cs - 1) * cs) / 2);
  loop invariant cs >= 0;
  loop invariant kmzf == cs * ((\at(a, Pre) % 28) + 10) - (cs * (cs - 1) * (cs + 1)) / 6;
  loop assigns yq, kmzf, cs;
*/
while (yq>cs) {
      yq -= cs;
      kmzf += yq;
      cs++;
  }
}