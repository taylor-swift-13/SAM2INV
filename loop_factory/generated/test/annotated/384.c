int main1(){
  int pf, w, pd2, ss7h;
  pf=1*5;
  w=0;
  pd2=5;
  ss7h=12;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ss7h == 12 + 7*w;
  loop invariant pd2 == 5 + 7*w;
  loop invariant w <= pf;
  loop invariant w >= 0;
  loop invariant pf == 5;
  loop assigns w, ss7h, pd2;
*/
while (1) {
      if (!(w<pf)) {
          break;
      }
      w += 1;
      ss7h = ss7h + 7;
      pd2 = pd2 + 7;
  }
}