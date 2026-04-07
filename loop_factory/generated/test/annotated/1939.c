int main1(){
  int b, ka, al7, o;
  b=(1%24)+10;
  ka=0;
  al7=0;
  o=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant al7 == ka;
  loop invariant (o + ka) == b;
  loop invariant (0 <= ka && ka <= b);
  loop invariant (0 <= o && o <= b);
  loop assigns ka, o, al7;
*/
while (1) {
      if (!(ka < b)) {
          break;
      }
      ka = ka + 1;
      o--;
      al7 += 1;
  }
}