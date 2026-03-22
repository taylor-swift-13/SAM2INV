int main1(int o){
  int b95, yu, z;

  b95=(o%20)+5;
  yu=(o%20)+5;
  z=(o%20)+5;

  while (b95>0) {
      if (yu>0) {
          if (z>0) {
              b95 -= 1;
              yu -= 1;
              z = z - 1;
          }
      }
  }

}
