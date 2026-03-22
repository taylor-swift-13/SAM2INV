int main1(){
  int pmz, ig, ermz, j0y, i, e, ibh, g5, mg6;

  pmz=1-6;
  ig=0;
  ermz=0;
  j0y=0;
  i=ig;
  e=pmz;
  ibh=13;
  g5=ig;
  mg6=ig;

  while (ig < pmz) {
      if (!(!(((ig % 2) == 0)))) {
          j0y += 2;
          ig++;
      }
      else {
          i = i + 1;
          g5 = g5 + 1;
          ig++;
      }
      if (ig+6<=i+pmz) {
          e = e+(-1);
      }
      ermz = ermz+(ig%2);
      ibh++;
      mg6 += g5;
      ibh = ibh + 3;
      ermz = ermz + 3;
  }

}
