int main1(){
  int mg, o, m, jti2, x, jj, i, f, ch, pd;
  mg=20;
  o=0;
  m=o;
  jti2=mg;
  x=mg;
  jj=o;
  i=1*3;
  f=o;
  ch=0;
  pd=mg;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ch == o;
  loop invariant m == o / 4;
  loop invariant f == (o + 2) / 4;
  loop invariant 0 <= pd;
  loop invariant 0 <= o <= mg;
  loop invariant 0 <= jj <= 7;
  loop invariant 0 <= i <= 7;
  loop invariant x >= mg;
  loop assigns o, jti2, x, m, f, ch, jj, i, pd;
*/
while (o < mg) {
      o = o + 1;
      jti2 = o % 4;
      x = x + jti2;
      if (jti2 == 0) {
          m++;
      }
      if (jti2 == 2) {
          f = f + 1;
      }
      ch = (1)+(ch);
      jj = (jj+x)%8;
      i = (i+f)%8;
      pd = jj+i+ch;
  }
}