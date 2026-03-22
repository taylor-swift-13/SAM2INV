int main1(int z,int c){
  int kwis, nw, x1k;

  kwis=0;
  nw=(z%28)+10;
  x1k=z;

  while (1) {
      if (!(nw>kwis)) {
          break;
      }
      nw -= kwis;
      kwis += 1;
      x1k = (kwis)+(x1k);
  }

}
