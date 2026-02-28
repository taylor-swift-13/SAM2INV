int main1(int a,int k){
  int g, w, i;

  g=(a%26)+19;
  w=0;
  i=k;

  while (1) {
      i = i+3;
      i = i+1;
      if (g<w+5) {
          i = i+6;
      }
  }

}
