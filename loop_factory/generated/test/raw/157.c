int main1(int o){
  int qsq5, z, b, su3m, puvk;

  qsq5=o*3;
  z=0;
  b=0;
  su3m=0;
  puvk=0;

  for (; z<qsq5; z += 1) {
      puvk++;
      su3m += 1;
      if (su3m>=6) {
          su3m -= 6;
          b += 1;
      }
  }

}
