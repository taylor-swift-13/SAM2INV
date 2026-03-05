int main56(int h){
  int zhe, c1, y1c;

  zhe=181;
  c1=zhe;
  y1c=(h%20)+5;

  while (1) {
      if (!(y1c>0)) {
          break;
      }
      h += c1;
      y1c = y1c - 1;
      h += 1;
  }

}
