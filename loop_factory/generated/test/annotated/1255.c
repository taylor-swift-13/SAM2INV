int main1(int g){
  int b89, rzv, de, i96, zs, nr7;
  b89=g+3;
  rzv=3;
  de=0;
  i96=g;
  zs=0;
  nr7=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(g,Pre) + 2*zs;
  loop invariant de == ((zs+2)*(zs+3)*(2*zs+5))/6 - 5;
  loop invariant rzv == 3 + zs;
  loop invariant b89 == \at(g, Pre) + 3;
  loop invariant de >= 0;
  loop assigns de, nr7, g, rzv, zs, i96;
*/
while (rzv<=b89) {
      de = de+rzv*rzv;
      nr7 = nr7+(de%2);
      g += 2;
      rzv = rzv + 1;
      zs = zs + 1;
      nr7 = nr7*nr7+i96;
      i96 = i96%4;
  }
}