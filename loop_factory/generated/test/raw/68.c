int main1(){
  int q, cl, g;

  q=1;
  cl=0;
  g=q;

  while (cl<q&&g>0) {
      g -= 1;
      cl = cl + 1;
      cl = cl+g+g;
      cl = cl + 1;
  }

}
