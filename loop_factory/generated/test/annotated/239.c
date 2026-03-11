int main1(){
  int pavv, yjt, tmi, e;
  pavv=1*5;
  yjt=0;
  tmi=0;
  e=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e <= pavv;
  loop invariant tmi >= 0;
  loop invariant pavv - tmi*yjt == 5;
  loop invariant pavv == 5;
  loop invariant tmi >= e + 1;
  loop assigns e, tmi;
*/
while (e<pavv) {
      tmi = tmi + 1;
      e += 1;
      if ((yjt%4)==0) {
          tmi += tmi;
      }
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pavv - tmi*yjt == 5;
  loop invariant tmi >= 0;
  loop invariant yjt >= 0;
  loop assigns pavv, yjt;
*/
while (1) {
      if (!(yjt-2>=0)) {
          break;
      }
      pavv += tmi;
      yjt++;
  }
}