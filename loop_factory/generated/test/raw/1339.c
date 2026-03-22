int main1(){
  int wc6o, sl5t, ogsm, ga;

  wc6o=(1%18)+18;
  sl5t=(1%40)+2;
  ogsm=0;
  ga=wc6o;

  while (sl5t!=ogsm) {
      ogsm = sl5t;
      ga += ogsm;
      sl5t = (sl5t+wc6o/sl5t)/2;
  }

}
