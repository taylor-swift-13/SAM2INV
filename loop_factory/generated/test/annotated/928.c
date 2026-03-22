int main1(int b){
  int we, c4, hujh, l;
  we=23;
  c4=0;
  hujh=6;
  l=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == we * c4;
  loop invariant (c4 <= we/2) ==> (hujh == 6);
  loop invariant (c4 > we/2) ==> (hujh == 6 + 2*(c4 - we/2));
  loop invariant ((c4 <= we/2) ==> hujh == 6) &&
                   ((c4 > we/2)  ==> hujh == 6 + 2 * (c4 - (we/2)));
  loop invariant 0 <= c4;
  loop invariant c4 <= we;
  loop assigns c4, l, hujh;
*/
while (c4<we) {
      if (c4>=we/2) {
          hujh += 2;
      }
      l += we;
      c4++;
  }
}