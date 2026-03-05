int main1(){
  int y, sc, v1a9;

  y=1;
  sc=-3;
  v1a9=3;

  while (sc<y) {
      v1a9 = sc%5;
      if (sc>=v1a9) {
          v1a9 = (sc-v1a9)%5;
          v1a9 = v1a9+v1a9-v1a9;
      }
      else {
          v1a9 = v1a9 + v1a9;
      }
      v1a9 = v1a9 + 1;
      sc++;
  }

}
