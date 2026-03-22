int main1(){
  int am, wew, sk, lem;
  am=1+24;
  wew=am;
  sk=am;
  lem=am;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant am == 1 + 24;
  loop invariant lem == 1 + 24;
  loop invariant wew >= 25;
  loop invariant sk == am * (wew - 24);
  loop assigns sk, wew;
*/
while (wew-3>=0) {
      if (!(!(wew<am/2))) {
          sk = sk + 1;
      }
      else {
          sk += lem;
      }
      wew = wew + 1;
  }
}