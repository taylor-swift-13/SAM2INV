int main1(){
  int he, neq, yh0;
  he=0;
  neq=(1%28)+10;
  yh0=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant neq == 11 - (he*(he - 1))/2;
  loop invariant yh0 >= 5;
  loop invariant he >= 0;
  loop invariant neq >= 0;
  loop assigns neq, yh0, he;
*/
while (neq>he) {
      neq = neq - he;
      yh0 = yh0+(neq%6);
      he++;
  }
}