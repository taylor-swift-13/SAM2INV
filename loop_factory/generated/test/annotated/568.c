int main1(){
  int v4, mnh, g, j1;
  v4=196;
  mnh=0;
  g=0;
  j1=v4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mnh == g % 6;
  loop invariant 0 <= g <= v4;
  loop invariant j1 == 196 + 15*(g/6) + ((g%6)*((g%6)+1))/2;
  loop invariant j1 == v4 + 15*(g/6) + ((g%6)*((g%6) + 1))/2;
  loop assigns g, j1, mnh;
*/
while (g<=v4-1) {
      mnh = (mnh+1)%6;
      g++;
      j1 = j1 + mnh;
  }
}