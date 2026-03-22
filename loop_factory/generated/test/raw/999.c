int main1(int m){
  int smi, fs, diu, h, mm;

  smi=116;
  fs=0;
  diu=0;
  h=0;
  mm=0;

  while (fs<smi) {
      h += 1;
      mm += 1;
      if (h>=4) {
          h -= 4;
          diu++;
      }
      fs++;
  }

}
