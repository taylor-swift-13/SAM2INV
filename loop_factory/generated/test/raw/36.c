int main1(int i){
  int d4, km, f;

  d4=i-9;
  km=0;
  f=km;

  while (1) {
      if (!(km<d4)) {
          break;
      }
      f = f + 1;
      km = km + 1;
      i += km;
  }

}
