int main1(){
  int fe, b, s682;
  fe=168;
  b=0;
  s682=fe;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (b <= fe);
  loop invariant (b == 0 && s682 == fe) || (b >= 1 && s682 == 0);
  loop assigns b, s682;
*/
while (b<fe) {
      b += 1;
      s682 = (fe)+(-(b));
      s682 = s682 - s682;
  }
}