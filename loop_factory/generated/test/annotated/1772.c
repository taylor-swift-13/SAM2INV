int main1(){
  int j9g, of, fr8s, o;
  j9g=1;
  of=0;
  fr8s=0;
  o=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= of;
  loop invariant of <= j9g;
  loop invariant o == (of*(of-1)*(2*of-1))/6;
  loop invariant fr8s <= 8*of;
  loop invariant fr8s >= 0;
  loop assigns o, of, fr8s;
*/
while (of < j9g) {
      o = o + of*of;
      of = of + 1;
      fr8s = fr8s+(o%9);
  }
}